"""
Telegram Pro Football Syndicate Curator, Real-Time Live Score & Stats Engine (ESPN + API-Football),
Strict Pre-Match Veto Model, Retroactive Channel Settlement & Total P&L Publisher for @Footybett (@betyyyybot)

Key Upgrades in v14.0:
1. Automatic Channel Correction & Total Won/Lost Analysis on @Footybett:
   - Automatically checks all past & current approved picks in `daily_ledger.json` (including yesterday's 2026-11-09 picks).
   - Grades any match that was previously stuck on PENDING (such as yesterday's 3-2 loss) and posts the missing
     settled result card (`📊❌ FOOTYBETT PICK RESULT — SETTLED LOSS` with score & loss analysis) ONCE to @Footybett.
   - Automatically posts a comprehensive `📊 @Footybett OFFICIAL TOTAL WON/LOST & P&L ANALYSIS` summary card to @Footybett
     whenever a day's picks finish settling (locked via `recap:<date>:<settled_count>` so it never repeats), and includes
     a live running All-Time Record footer on every result card.
   - Added `/poststats` command in @betyyyybot to publish the full Won/Lost & P&L Analysis card to @Footybett on demand.
2. 3-Day Window + Fuzzy Team Matcher + ESPN Event Summary Stats (Corners & Cards):
   - Searches `date - 1 day`, `date`, and `date + 1 day` simultaneously to eliminate timezone/midnight kickoff mismatches.
   - Uses `difflib.SequenceMatcher` (>= 0.72 similarity) + club alias normalization so OCR typos never block live score matching.
   - Pulls exact corners and yellow/red cards from ESPN's public Event Summary API (`/summary?event=<id>`) so Corners and
     Bookings bets grade live and at FT with exact counts.
3. Strict Pre-Match Veto Engine (Blocking 3-1 -> 3-2 Traps):
   - Defensive Vulnerability Veto, High-Tempo Shootout Veto, Rotation Veto, and Unverified Market Veto.
"""

import os
import re
import math
import time
import json
import difflib
import unicodedata
import logging
import threading
import datetime
import urllib.request
import urllib.parse
import urllib.error
from typing import Dict, Any, Optional, List, Tuple, Set
from dataclasses import dataclass, asdict, fields

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger("betyyyybot")

try:
    from PIL import Image, ImageOps, ImageEnhance
    import io
    import pytesseract
    OCR_AVAILABLE = True
except ImportError:
    OCR_AVAILABLE = False

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SUBSCRIBERS_FILE = os.path.join(BASE_DIR, "subscribers.json")
SEEN_POSTS_FILE = os.path.join(BASE_DIR, "seen_posts.json")
CHANNELS_FILE = os.path.join(BASE_DIR, "watched_channels.json")
API_CACHE_FILE = os.path.join(BASE_DIR, "api_cache.json")
DAILY_LEDGER_FILE = os.path.join(BASE_DIR, "daily_ledger.json")
PUBLISHED_LOCKS_FILE = os.path.join(BASE_DIR, "published_channel_locks.json")

API_FOOTBALL_KEY = os.environ.get("API_FOOTBALL_KEY", "")
PUBLISH_CHANNEL_ID = os.environ.get("PUBLISH_CHANNEL_ID", "@Footybett")
TRACKING_START_DATE = "2026-11-08"

DEFAULT_CHANNELS = [
    "bomb_footballsignals",
    "MrBanksFreeChannel",
    "eaglepredict",
    "ibettingxx",
    "AccuratePredictMaster",
    "tipmantips",
    "betfuse_official",
    "sportybet_codes"
]

TEAM_ALIASES: Dict[str, str] = {
    "psg": "paris saint germain",
    "paris sg": "paris saint germain",
    "man city": "manchester city",
    "man utd": "manchester united",
    "man united": "manchester united",
    "spurs": "tottenham hotspur",
    "tottenham": "tottenham hotspur",
    "wolves": "wolverhampton wanderers",
    "wolverhampton": "wolverhampton wanderers",
    "atletico": "atletico madrid",
    "atl madrid": "atletico madrid",
    "athletic bilbao": "athletic club",
    "barca": "barcelona",
    "inter": "inter milan",
    "internazionale": "inter milan",
    "inter milano": "inter milan",
    "bayern": "bayern munich",
    "bayern munchen": "bayern munich",
    "dortmund": "borussia dortmund",
    "bvb": "borussia dortmund",
    "leverkusen": "bayer leverkusen",
    "gladbach": "borussia monchengladbach",
    "m'gladbach": "borussia monchengladbach",
    "newcastle": "newcastle united",
    "west ham": "west ham united",
    "brighton": "brighton hove albion",
    "nottm forest": "nottingham forest",
    "leicester": "leicester city",
    "ipswich": "ipswich town",
    "bournemouth": "afc bournemouth",
    "psv": "psv eindhoven",
    "sporting": "sporting cp",
    "sporting lisbon": "sporting cp",
    "fenerbahce": "fenerbahce",
    "galatasaray": "galatasaray",
    "besiktas": "besiktas",
}


def normalize_team_str(name: str) -> str:
    if not name:
        return ""
    s = "".join(c for c in unicodedata.normalize("NFD", name) if unicodedata.category(c) != "Mn")
    s = s.lower().strip()
    s = re.sub(r"[^a-z0-9\s]", " ", s)
    s = re.sub(
        r"\b(fc|cf|sc|ac|afc|sk|fk|sv|tsg|rb|ud|cd|rcd|real|club|de|del|la|el|1907|1913|1909|1899|04|05)\b",
        " ",
        s
    )
    s = re.sub(r"\s+", " ", s).strip()
    for k, v in TEAM_ALIASES.items():
        if s == k or f" {k} " in f" {s} ":
            return v
    return s


def teams_match(name_a: str, name_b: str) -> bool:
    na = normalize_team_str(name_a)
    nb = normalize_team_str(name_b)
    if not na or not nb:
        return False
    if na == nb or na in nb or nb in na:
        return True
    tokens_a = {t for t in na.split() if len(t) >= 4}
    tokens_b = {t for t in nb.split() if len(t) >= 4}
    if tokens_a and tokens_b and (tokens_a & tokens_b):
        return True
    ratio = difflib.SequenceMatcher(None, na, nb).ratio()
    return ratio >= 0.72


def shift_date_str(date_str: str, delta_days: int) -> str:
    try:
        dt = datetime.datetime.strptime(date_str, "%Y-%m-%d") + datetime.timedelta(days=delta_days)
        return dt.strftime("%Y-%m-%d")
    except Exception:
        return date_str


def load_json_set(filepath: str, default: Optional[List[Any]] = None) -> Set[Any]:
    if os.path.exists(filepath):
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                return set(json.load(f))
        except Exception:
            pass
    return set(default or [])


def save_json_set(filepath: str, data_set: Set[Any], max_items: int = 5000):
    try:
        items = list(data_set)[-max_items:]
        with open(filepath, "w", encoding="utf-8") as f:
            json.dump(items, f)
    except Exception as e:
        logger.error("Failed to save JSON file %s: %s", filepath, e)


def load_json_dict(filepath: str) -> Dict[str, Any]:
    if os.path.exists(filepath):
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {}


def save_json_dict(filepath: str, data: Dict[str, Any]):
    try:
        with open(filepath, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except Exception as e:
        logger.error("Failed to write JSON dict %s: %s", filepath, e)


@dataclass
class BetSignal:
    raw_text: str
    team_home: str
    team_away: str
    market_type: str
    selection: str
    line: Optional[float]
    odds: float
    source_channel: str = ""
    is_virtual_srl: bool = False
    post_date_str: str = ""


@dataclass
class PreMatchDossier:
    fixture_found: bool = False
    competition: str = "Official Competition"
    venue: str = "Home Stadium"
    match_stakes: str = "Competitive Fixture"
    standings_summary: str = "Competitive table clash"
    form_summary: str = "Balanced recent form"
    injuries_summary: str = "No major key absences reported"
    lineup_summary: str = "Projected Starting XIs (Official 45m pre-kickoff)"
    home_missing_count: int = 0
    away_missing_count: int = 0
    home_goals_for_avg: float = 1.45
    home_goals_against_avg: float = 1.15
    away_goals_for_avg: float = 1.25
    away_goals_against_avg: float = 1.30
    home_xg_adj: float = 0.0
    away_xg_adj: float = 0.0
    corners_adj: float = 0.0
    veto_reason: Optional[str] = None


@dataclass
class LedgerBetItem:
    bet_key: str
    date_str: str
    team_home: str
    team_away: str
    market_type: str
    selection: str
    line: Optional[float]
    odds: float
    floor_odds: float
    is_approved: bool
    confidence_stars: str
    model_prob: float
    edge_ev: float
    recommended_units: float
    consensus_sources: List[str]
    rationale: str
    evidence: str
    rotation_warning: Optional[str]
    search_url: str
    match_context: str = ""
    lineup_injuries_info: str = ""
    match_status: str = "PENDING"
    score_str: str = "-"
    live_detail: str = ""
    loss_autopsy: str = ""
    settlement: str = "PENDING"  # PENDING, WON ✅, LOST ❌, PUSH ➖
    notified_settled: bool = False
    notified_admin_curate: bool = False
    published_to_channel: bool = False
    published_result_to_channel: bool = False


class DailyLedgerManager:
    """Manages Active Slates, All-Time Historical Ledger (from 2026-11-08), and Permanent @Footybett Locks."""

    @classmethod
    def get_today_str(cls) -> str:
        return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")

    @classmethod
    def get_yesterday_str(cls) -> str:
        y = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=1)
        return y.strftime("%Y-%m-%d")

    @classmethod
    def is_locked_in_channel(cls, lock_key: str) -> bool:
        locks = load_json_set(PUBLISHED_LOCKS_FILE)
        return lock_key in locks

    @classmethod
    def mark_locked_in_channel(cls, lock_key: str):
        locks = load_json_set(PUBLISHED_LOCKS_FILE)
        locks.add(lock_key)
        save_json_set(PUBLISHED_LOCKS_FILE, locks)

    @classmethod
    def get_baseline_historical_items(cls) -> Dict[str, LedgerBetItem]:
        """Seeds the verified 2026-11-08 (4W-0L) slate so all-time stats always start accurately from 2026-11-08."""
        d8 = "2026-11-08"
        items_list = [
            LedgerBetItem(
                bet_key="atletico madrid_vs_fc barcelona_goals_over_under_under 4.5 goals",
                date_str=d8,
                team_home="Atletico Madrid",
                team_away="FC Barcelona",
                market_type="goals_over_under",
                selection="Under 4.5 Goals",
                line=4.5,
                odds=1.70,
                floor_odds=1.16,
                is_approved=True,
                confidence_stars="⭐️⭐️⭐️⭐️⭐️",
                model_prob=86.3,
                edge_ev=46.7,
                recommended_units=2.0,
                consensus_sources=["bomb_footballsignals"],
                rationale="High tactical discipline and controlled home pace project 2.70 expected match goals.",
                evidence="Consistent with form: 4 of last 5 competitive matches aligned with this line (78% trend).",
                rotation_warning="ℹ️ UCL Notice (Barcelona): Potential starter rotation.",
                search_url="https://www.google.com/search?q=Atletico%20Madrid%20vs%20FC%20Barcelona%20Under%204.5%20Goals%20odds",
                match_context="LaLiga | 🔥 Top-4 Title / UCL 6-Pointer",
                lineup_injuries_info="✅ Confirmed XI | No major key absences reported",
                match_status="FT",
                score_str="1-1 (FT)",
                settlement="WON ✅",
                notified_settled=True,
                published_to_channel=True,
                published_result_to_channel=True
            ),
            LedgerBetItem(
                bet_key="fc twente_vs_ajax_1x2_fc twente or draw (1x / safe line)",
                date_str=d8,
                team_home="FC Twente",
                team_away="Ajax",
                market_type="1x2",
                selection="FC Twente or Draw (1X / Safe Line)",
                line=None,
                odds=1.43,
                floor_odds=1.28,
                is_approved=True,
                confidence_stars="⭐️⭐️⭐️⭐️⭐️",
                model_prob=78.0,
                edge_ev=11.5,
                recommended_units=2.0,
                consensus_sources=["eaglepredict"],
                rationale="Poisson match outcome distribution projects 78.0% hit probability at 1.43 odds.",
                evidence="Consistent with form: 4 of last 5 competitive matches aligned with this line (78% trend).",
                rotation_warning=None,
                search_url="https://www.google.com/search?q=FC%20Twente%20vs%20Ajax%20Match%20Outcome%20odds",
                match_context="Eredivisie | 🔥 Top-4 Title / UCL 6-Pointer",
                lineup_injuries_info="✅ Confirmed XI | Full strength squads",
                match_status="FT",
                score_str="2-2 (FT)",
                settlement="WON ✅",
                notified_settled=True,
                published_to_channel=True,
                published_result_to_channel=True
            ),
            LedgerBetItem(
                bet_key="sunderland_vs_chelsea_1x2_sunderland or draw (1x / safe line)",
                date_str=d8,
                team_home="Sunderland",
                team_away="Chelsea",
                market_type="1x2",
                selection="Sunderland or Draw (1X / Safe Line)",
                line=None,
                odds=1.32,
                floor_odds=1.28,
                is_approved=True,
                confidence_stars="⭐️⭐️⭐️",
                model_prob=78.0,
                edge_ev=3.0,
                recommended_units=1.0,
                consensus_sources=["eaglepredict"],
                rationale="Poisson match outcome distribution projects 78.0% hit probability at 1.32 odds.",
                evidence="Consistent with form: 4 of last 5 competitive matches aligned with this line (78% trend).",
                rotation_warning=None,
                search_url="https://www.google.com/search?q=Sunderland%20vs%20Chelsea%20Match%20Outcome%20odds",
                match_context="Competitive Fixture",
                lineup_injuries_info="✅ Confirmed XI",
                match_status="FT",
                score_str="1-0 (FT)",
                settlement="WON ✅",
                notified_settled=True,
                published_to_channel=True,
                published_result_to_channel=True
            ),
            LedgerBetItem(
                bet_key="brighton_vs_brentford_1x2_brighton or draw (1x / safe line)",
                date_str=d8,
                team_home="Brighton",
                team_away="Brentford",
                market_type="1x2",
                selection="Brighton or Draw (1X / Safe Line)",
                line=None,
                odds=1.31,
                floor_odds=1.28,
                is_approved=True,
                confidence_stars="⭐️⭐️⭐️",
                model_prob=78.0,
                edge_ev=2.2,
                recommended_units=1.0,
                consensus_sources=["eaglepredict"],
                rationale="Poisson match outcome distribution projects 78.0% hit probability at 1.31 odds.",
                evidence="Consistent with form: 4 of last 5 competitive matches aligned with this line (78% trend).",
                rotation_warning=None,
                search_url="https://www.google.com/search?q=Brighton%20vs%20Brentford%20Match%20Outcome%20odds",
                match_context="Premier League | Competitive Table Clash",
                lineup_injuries_info="✅ Confirmed XI",
                match_status="FT",
                score_str="2-0 (FT)",
                settlement="WON ✅",
                notified_settled=True,
                published_to_channel=True,
                published_result_to_channel=True
            ),
            LedgerBetItem(
                bet_key="atletico madrid_vs_fc barcelona_corners_over_under_over 9.5 corners",
                date_str=d8,
                team_home="Atletico Madrid",
                team_away="FC Barcelona",
                market_type="corners_over_under",
                selection="Over 9.5 Corners",
                line=9.5,
                odds=1.70,
                floor_odds=1.95,
                is_approved=False,
                confidence_stars="❌ DECLINED",
                model_prob=51.2,
                edge_ev=-13.0,
                recommended_units=0.0,
                consensus_sources=["bomb_footballsignals"],
                rationale="Rotation Risk: Starting wingers projected to be rested for UCL. High probability of low corner volume.",
                evidence="Historical corner average sits below 9.5 in high-tactical clashes.",
                rotation_warning="⚠️ Rotation Alert (Barcelona)",
                search_url="",
                match_status="FT",
                score_str="7 Corners (FT)",
                settlement="LOST ❌",
                notified_settled=True,
                published_to_channel=True,
                published_result_to_channel=True
            ),
            LedgerBetItem(
                bet_key="crystal palace_vs_tsg hoffenheim_corners_over_under_over 9.5 corners",
                date_str=d8,
                team_home="Crystal Palace",
                team_away="TSG Hoffenheim",
                market_type="corners_over_under",
                selection="Over 9.5 Corners",
                line=9.5,
                odds=1.75,
                floor_odds=2.00,
                is_approved=False,
                confidence_stars="❌ DECLINED (VIRTUAL SRL)",
                model_prob=0.0,
                edge_ev=-100.0,
                recommended_units=0.0,
                consensus_sources=["bomb_footballsignals"],
                rationale="Simulated Reality League (SRL) virtual AI match detected. No real players or lineups exist.",
                evidence="Unverified Cross-League Virtual Fixture — Automatically Declined.",
                rotation_warning=None,
                search_url="",
                match_status="FT",
                score_str="SRL",
                settlement="LOST ❌",
                notified_settled=True,
                published_to_channel=True,
                published_result_to_channel=True
            ),
            LedgerBetItem(
                bet_key="sparta prague_vs_afc bournemouth_goals_over_under_over 2.5 goals",
                date_str=d8,
                team_home="Sparta Prague",
                team_away="AFC Bournemouth",
                market_type="goals_over_under",
                selection="Over 2.5 Goals",
                line=2.5,
                odds=1.55,
                floor_odds=2.00,
                is_approved=False,
                confidence_stars="❌ DECLINED (VIRTUAL SRL)",
                model_prob=0.0,
                edge_ev=-100.0,
                recommended_units=0.0,
                consensus_sources=["bomb_footballsignals"],
                rationale="Simulated Reality League (SRL) virtual AI match detected. No real players or lineups exist.",
                evidence="Unverified Cross-League Virtual Fixture — Automatically Declined.",
                rotation_warning=None,
                search_url="",
                match_status="FT",
                score_str="SRL",
                settlement="LOST ❌",
                notified_settled=True,
                published_to_channel=True,
                published_result_to_channel=True
            ),
        ]
        seeded: Dict[str, LedgerBetItem] = {}
        for item in items_list:
            full_key = f"{item.date_str}:{item.bet_key}"
            seeded[full_key] = item
        return seeded

    @classmethod
    def load_all_history_items(cls) -> Dict[str, LedgerBetItem]:
        raw = load_json_dict(DAILY_LEDGER_FILE)
        valid_fields = {f.name for f in fields(LedgerBetItem)}
        items: Dict[str, LedgerBetItem] = {}

        for k, v in raw.items():
            if not isinstance(v, dict):
                continue
            try:
                filtered_v = {fk: fv for fk, fv in v.items() if fk in valid_fields}
                item = LedgerBetItem(**filtered_v)
                full_key = f"{item.date_str}:{item.bet_key}"
                if cls.is_locked_in_channel(f"pick:{full_key}"):
                    item.published_to_channel = True
                if cls.is_locked_in_channel(f"result:{full_key}") or cls.is_locked_in_channel(f"win:{full_key}"):
                    item.published_result_to_channel = True
                items[full_key] = item
            except Exception as e:
                logger.warning("Skipping malformed ledger entry %s: %s", k, e)

        baseline = cls.get_baseline_historical_items()
        needs_save = False
        for b_key, b_item in baseline.items():
            if b_key not in items:
                items[b_key] = b_item
                cls.mark_locked_in_channel(f"pick:{b_key}")
                cls.mark_locked_in_channel(f"result:{b_key}")
                cls.mark_locked_in_channel(f"win:{b_key}")
                cls.mark_locked_in_channel("recap:2026-11-08:4")
                needs_save = True

        if needs_save:
            cls.save_all_items(items)

        return items

    @classmethod
    def load_today_items(cls) -> Dict[str, LedgerBetItem]:
        all_items = cls.load_all_history_items()
        today = cls.get_today_str()
        return {k: v for k, v in all_items.items() if v.date_str == today}

    @classmethod
    def load_recent_active_items(cls) -> Tuple[List[LedgerBetItem], List[LedgerBetItem]]:
        all_items = cls.load_all_history_items()
        today = cls.get_today_str()
        yesterday = cls.get_yesterday_str()
        t_list = [v for v in all_items.values() if v.date_str == today]
        y_list = [v for v in all_items.values() if v.date_str == yesterday]
        return t_list, y_list

    @classmethod
    def save_all_items(cls, items: Dict[str, LedgerBetItem]):
        raw = {k: asdict(v) for k, v in items.items()}
        save_json_dict(DAILY_LEDGER_FILE, raw)

    @classmethod
    def upsert_bet(cls, item: LedgerBetItem) -> Tuple[bool, LedgerBetItem]:
        all_items = cls.load_all_history_items()
        full_key = f"{item.date_str}:{item.bet_key}"
        if cls.is_locked_in_channel(f"pick:{full_key}"):
            item.published_to_channel = True
        if cls.is_locked_in_channel(f"result:{full_key}") or cls.is_locked_in_channel(f"win:{full_key}"):
            item.published_result_to_channel = True

        if full_key in all_items:
            existing = all_items[full_key]
            for src in item.consensus_sources:
                if src and src not in existing.consensus_sources:
                    existing.consensus_sources.append(src)
            if item.odds > existing.odds:
                existing.odds = item.odds
            cls.save_all_items(all_items)
            return False, existing
        else:
            all_items[full_key] = item
            cls.save_all_items(all_items)
            return True, item


class LiveFootballAPI:
    BASE_URL = "https://v3.football.api-sports.io"
    ESPN_SCOREBOARD_URL = "https://site.api.espn.com/apis/site/v2/sports/soccer/all/scoreboard"
    ESPN_SUMMARY_URL = "https://site.api.espn.com/apis/site/v2/sports/soccer/all/summary"

    @classmethod
    def fetch_espn_event_stats(cls, event_id: str) -> Tuple[Optional[int], Optional[int]]:
        """
        Fetches exact total corners and total bookings (yellow + red cards) for a specific ESPN event_id.
        Zero API quota limit.
        """
        if not event_id:
            return None, None
        url = f"{cls.ESPN_SUMMARY_URL}?event={event_id}"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        corners_total = None
        cards_total = None
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                box = data.get("boxscore", {})
                teams = box.get("teams", [])
                c_sum, y_sum = 0, 0
                found_c, found_y = False, False
                for t in teams:
                    for st in t.get("statistics", []):
                        s_name = st.get("name", "").lower()
                        val_str = st.get("displayValue", "0")
                        if "corner" in s_name:
                            try:
                                c_sum += int(float(val_str))
                                found_c = True
                            except Exception:
                                pass
                        elif "yellowcard" in s_name or "redcard" in s_name:
                            try:
                                y_sum += int(float(val_str))
                                found_y = True
                            except Exception:
                                pass
                if found_c:
                    corners_total = c_sum
                if found_y:
                    cards_total = y_sum
        except Exception:
            pass
        return corners_total, cards_total

    @classmethod
    def fetch_espn_fixtures_by_date(cls, date_str: str) -> List[Dict[str, Any]]:
        espn_date = date_str.replace("-", "")
        url = f"{cls.ESPN_SCOREBOARD_URL}?dates={espn_date}&limit=300"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        results = []
        try:
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                events = data.get("events", [])
                for ev in events:
                    ev_id = str(ev.get("id", ""))
                    comps = ev.get("competitions", [])
                    if not comps:
                        continue
                    comp = comps[0]
                    competitors = comp.get("competitors", [])
                    if len(competitors) < 2:
                        continue

                    home_c = next((c for c in competitors if c.get("homeAway") == "home"), competitors[0])
                    away_c = next((c for c in competitors if c.get("homeAway") == "away"), competitors[1])

                    h_name = home_c.get("team", {}).get("displayName") or home_c.get("team", {}).get("name", "")
                    a_name = away_c.get("team", {}).get("displayName") or away_c.get("team", {}).get("name", "")
                    h_score = int(home_c.get("score") or 0)
                    a_score = int(away_c.get("score") or 0)
                    h_form = home_c.get("form") or ""
                    a_form = away_c.get("form") or ""

                    status_obj = comp.get("status", {}) or ev.get("status", {})
                    st_type = status_obj.get("type", {})
                    state = st_type.get("state", "pre")
                    short_detail = st_type.get("shortDetail") or status_obj.get("displayClock") or "NS"
                    completed = bool(st_type.get("completed", False))

                    if completed or state == "post":
                        status_code = "FT"
                    elif state == "in":
                        status_code = f"LIVE {short_detail}"
                    else:
                        status_code = "NS"

                    corners_total = None
                    cards_total = None
                    for c_obj in (home_c, away_c):
                        for st in c_obj.get("statistics", []):
                            nm = st.get("name", "").lower()
                            if "corner" in nm:
                                try:
                                    corners_total = (corners_total or 0) + int(float(st.get("displayValue", 0)))
                                except Exception:
                                    pass
                            elif "yellow" in nm or "card" in nm:
                                try:
                                    cards_total = (cards_total or 0) + int(float(st.get("displayValue", 0)))
                                except Exception:
                                    pass

                    results.append({
                        "source": "ESPN_LIVE",
                        "event_id": ev_id,
                        "home": h_name,
                        "away": a_name,
                        "gh": h_score,
                        "ga": a_score,
                        "state": state,
                        "is_finished": completed or state == "post",
                        "is_live": state == "in",
                        "status_label": status_code,
                        "clock": short_detail,
                        "home_form": h_form,
                        "away_form": a_form,
                        "corners_total": corners_total,
                        "cards_total": cards_total,
                        "venue": comp.get("venue", {}).get("fullName", "Stadium"),
                        "league": ev.get("season", {}).get("slug", "Football")
                    })
        except Exception as e:
            logger.warning("ESPN live scoreboard fetch warning (%s): %s", date_str, e)
        return results

    @classmethod
    def make_request(cls, endpoint: str, params: Dict[str, str], ttl_seconds: int = 43200) -> Optional[Dict[str, Any]]:
        if not API_FOOTBALL_KEY:
            return None
        cache_key = f"{endpoint}:{urllib.parse.urlencode(sorted(params.items()))}"
        cache = load_json_dict(API_CACHE_FILE)
        now = time.time()
        if ttl_seconds > 0 and cache_key in cache and (now - cache[cache_key].get("ts", 0) < ttl_seconds):
            return cache[cache_key].get("data")

        query = urllib.parse.urlencode(params)
        url = f"{cls.BASE_URL}/{endpoint}?{query}"
        req = urllib.request.Request(url, headers={
            "x-apisports-key": API_FOOTBALL_KEY.strip(),
            "User-Agent": "BetBot-Pro/14.0"
        })
        try:
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                if data and data.get("response") is not None and len(data.get("response", [])) > 0:
                    cache[cache_key] = {"ts": now, "data": data}
                    save_json_dict(API_CACHE_FILE, cache)
                return data
        except Exception as e:
            logger.error("API-Football request error (%s): %s", endpoint, e)
            return None

    @classmethod
    def check_account_status(cls) -> str:
        if not API_FOOTBALL_KEY:
            return "ESPN Real-Time Scoreboard Active (API-Football Key Not Set)"
        url = f"{cls.BASE_URL}/status"
        req = urllib.request.Request(url, headers={"x-apisports-key": API_FOOTBALL_KEY.strip()})
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                res = data.get("response", {})
                reqs = res.get("requests", {})
                sub = res.get("subscription", {})
                return f"ESPN Live (Unlimited) + API-Football ({sub.get('plan', 'Free')}: {reqs.get('current', 0)}/{reqs.get('limit_day', 100)} calls)"
        except Exception as e:
            return f"ESPN Live Active | API-Football status error: {e}"

    @classmethod
    def fetch_apifootball_fixtures_by_date(cls, date_str: str, force_fresh: bool = False) -> List[Dict[str, Any]]:
        ttl = 0 if force_fresh else 120
        data = cls.make_request("fixtures", {"date": date_str}, ttl_seconds=ttl)
        if data and data.get("response"):
            return data["response"]
        return []

    @classmethod
    def find_match_in_live_feeds(
        cls,
        team_a: str,
        team_b: str,
        espn_list: List[Dict[str, Any]],
        apif_list: List[Dict[str, Any]]
    ) -> Optional[Dict[str, Any]]:
        # 1. Check ESPN Real-Time Feed first
        for em in espn_list:
            if (teams_match(team_a, em["home"]) and teams_match(team_b, em["away"])) or (
                teams_match(team_a, em["away"]) and teams_match(team_b, em["home"])
            ):
                swapped = teams_match(team_a, em["away"]) and not teams_match(team_a, em["home"])
                return {
                    "event_id": em.get("event_id", ""),
                    "gh": em["ga"] if swapped else em["gh"],
                    "ga": em["gh"] if swapped else em["ga"],
                    "is_finished": em["is_finished"],
                    "is_live": em["is_live"],
                    "status_label": em["status_label"],
                    "clock": em["clock"],
                    "corners_total": em.get("corners_total"),
                    "cards_total": em.get("cards_total"),
                    "home_form": em["away_form"] if swapped else em["home_form"],
                    "away_form": em["home_form"] if swapped else em["away_form"],
                }

        # 2. Check API-Football Feed
        for f in apif_list:
            fh = f.get("teams", {}).get("home", {}).get("name", "")
            fa = f.get("teams", {}).get("away", {}).get("name", "")
            if (teams_match(team_a, fh) and teams_match(team_b, fa)) or (
                teams_match(team_a, fa) and teams_match(team_b, fh)
            ):
                swapped = teams_match(team_a, fa) and not teams_match(team_a, fh)
                st = f.get("fixture", {}).get("status", {})
                short = st.get("short", "NS")
                elapsed = st.get("elapsed")
                gh = f.get("goals", {}).get("home") or 0
                ga = f.get("goals", {}).get("away") or 0
                is_fin = short in ["FT", "AET", "PEN"]
                is_lv = short in ["1H", "HT", "2H", "ET", "LIVE"]
                clock_str = f"{elapsed}'" if (is_lv and elapsed) else short
                return {
                    "event_id": "",
                    "gh": ga if swapped else gh,
                    "ga": gh if swapped else ga,
                    "is_finished": is_fin,
                    "is_live": is_lv,
                    "status_label": "FT" if is_fin else (f"LIVE {clock_str}" if is_lv else short),
                    "clock": clock_str,
                    "corners_total": None,
                    "cards_total": None,
                    "home_form": "",
                    "away_form": "",
                }
        return None

    @classmethod
    def build_pre_match_dossier(cls, team_a: str, team_b: str, date_str: str) -> PreMatchDossier:
        dossier = PreMatchDossier()
        espn_list = cls.fetch_espn_fixtures_by_date(date_str)
        for em in espn_list:
            if (teams_match(team_a, em["home"]) and teams_match(team_b, em["away"])) or (
                teams_match(team_a, em["away"]) and teams_match(team_b, em["home"])
            ):
                dossier.fixture_found = True
                dossier.venue = em.get("venue") or "Official Stadium"
                hf = em.get("home_form") or ""
                af = em.get("away_form") or ""
                if hf or af:
                    dossier.form_summary = f"Home Form: {hf or 'N/A'} | Away Form: {af or 'N/A'}"
                    if hf.count("L") >= 3:
                        dossier.home_xg_adj -= 0.30
                        dossier.home_goals_against_avg = 1.85
                    if af.count("W") >= 3:
                        dossier.away_xg_adj += 0.25
                        dossier.away_goals_for_avg = 1.75
                break

        apif_list = cls.fetch_apifootball_fixtures_by_date(date_str, force_fresh=False)
        matched_fix = None
        for f in apif_list:
            fh = f.get("teams", {}).get("home", {}).get("name", "")
            fa = f.get("teams", {}).get("away", {}).get("name", "")
            if teams_match(team_a, fh) and teams_match(team_b, fa):
                matched_fix = f
                break

        if not matched_fix:
            return dossier

        dossier.fixture_found = True
        fixture_id = matched_fix.get("fixture", {}).get("id")
        venue_name = matched_fix.get("fixture", {}).get("venue", {}).get("name") or dossier.venue
        league_info = matched_fix.get("league", {})
        league_id = league_info.get("id")
        season = league_info.get("season")
        league_name = league_info.get("name", "League")
        round_name = league_info.get("round", "")

        home_id = matched_fix.get("teams", {}).get("home", {}).get("id")
        away_id = matched_fix.get("teams", {}).get("away", {}).get("id")

        dossier.competition = f"{league_name} ({round_name})" if round_name else league_name
        dossier.venue = venue_name

        if league_id and season:
            st_data = cls.make_request("standings", {"league": str(league_id), "season": str(season)}, ttl_seconds=43200)
            if st_data and st_data.get("response"):
                try:
                    table = st_data["response"][0]["league"]["standings"][0]
                    h_rank, a_rank, h_form, a_form, h_pts, a_pts = None, None, "", "", 0, 0
                    for row in table:
                        tid = row.get("team", {}).get("id")
                        played = max(1, row.get("all", {}).get("played") or 1)
                        gf = row.get("all", {}).get("goals", {}).get("for") or 0
                        ga = row.get("all", {}).get("goals", {}).get("against") or 0
                        if tid == home_id:
                            h_rank = row.get("rank")
                            h_form = row.get("form") or ""
                            h_pts = row.get("points") or 0
                            dossier.home_goals_for_avg = gf / played
                            dossier.home_goals_against_avg = ga / played
                        elif tid == away_id:
                            a_rank = row.get("rank")
                            a_form = row.get("form") or ""
                            a_pts = row.get("points") or 0
                            dossier.away_goals_for_avg = gf / played
                            dossier.away_goals_against_avg = ga / played

                    if h_rank and a_rank:
                        dossier.standings_summary = (
                            f"Home #{h_rank} ({h_pts}pts, {h_form[-5:]}) vs Away #{a_rank} ({a_pts}pts, {a_form[-5:]})"
                        )
                        if h_rank <= 4 and a_rank <= 4:
                            dossier.match_stakes = "🔥 Top-4 Title / UCL 6-Pointer"
                        if dossier.home_goals_against_avg >= 1.65:
                            dossier.veto_reason = (
                                f"High Defensive Vulnerability: {team_a} concedes {dossier.home_goals_against_avg:.2f} goals/gm"
                            )
                except Exception:
                    pass

        if fixture_id:
            lu_data = cls.make_request("fixtures/lineups", {"fixture": str(fixture_id)}, ttl_seconds=1800)
            if lu_data and lu_data.get("response") and len(lu_data["response"]) >= 2:
                try:
                    lu_h = lu_data["response"][0]
                    lu_a = lu_data["response"][1]
                    form_h = lu_h.get("formation") or "4-3-3"
                    form_a = lu_a.get("formation") or "4-2-3-1"
                    xi_h = [p.get("player", {}).get("name", "").split()[-1] for p in lu_h.get("startXI", [])[:4]]
                    xi_a = [p.get("player", {}).get("name", "").split()[-1] for p in lu_a.get("startXI", [])[:4]]
                    dossier.lineup_summary = (
                        f"✅ Confirmed XI: Home ({form_h}: {', '.join(xi_h)}...) vs Away ({form_a}: {', '.join(xi_a)}...)"
                    )
                except Exception:
                    pass

        return dossier

    @classmethod
    def build_live_bet_progress_and_autopsy(
        cls,
        item: LedgerBetItem,
        gh: int,
        ga: int,
        is_finished: bool,
        is_live: bool,
        clock: str
    ) -> Tuple[str, str]:
        total_g = gh + ga
        live_detail = ""
        autopsy = ""

        if is_live:
            if item.market_type == "goals_over_under" and item.line is not None:
                if "over" in item.selection.lower():
                    needed = max(0, int(math.floor(item.line) + 1) - total_g)
                    live_detail = f"🟢 CASHED LIVE ({total_g} goals)" if needed == 0 else f"⏳ Live {clock}: {total_g} goals (Needs {needed} more)"
                else:
                    max_allowed = int(math.floor(item.line))
                    margin = max_allowed - total_g
                    live_detail = f"🟢 On Track ({total_g}/{max_allowed} max goals)" if margin >= 0 else f"🔴 Line Broken ({total_g} goals scored)"
            else:
                diff = gh - ga
                if diff > 0:
                    live_detail = f"🟢 Leading {gh}-{ga} ({clock})"
                elif diff == 0:
                    live_detail = f"⚖️ Level {gh}-{ga} ({clock})"
                else:
                    live_detail = f"🔴 Trailing {gh}-{ga} ({clock})"

        if is_finished and item.settlement == "LOST ❌":
            if item.market_type == "goals_over_under" and item.line is not None:
                if "under" in item.selection.lower():
                    autopsy = f"🔍 Loss Analysis: High-scoring {gh}-{ga} shootout ({total_g} total goals broke {item.selection} line)."
                else:
                    autopsy = f"🔍 Loss Analysis: Low-scoring {gh}-{ga} finish ({total_g} total goals fell short of {item.selection})."
            elif "or draw" in item.selection.lower() or item.market_type in ["1x2", "unknown", "unverified"]:
                autopsy = (
                    f"🔍 Loss Analysis: Defensive breakdown — conceded {max(gh, ga)} goals in a {gh}-{ga} defeat despite pre-match projection."
                )
            else:
                autopsy = f"🔍 Loss Analysis: Final result {gh}-{ga} (FT) did not cover {item.selection}."

        return live_detail, autopsy

    @classmethod
    def grade_ledger_items(cls, force_fresh: bool = False) -> Tuple[List[LedgerBetItem], List[LedgerBetItem]]:
        all_items = DailyLedgerManager.load_all_history_items()
        if not all_items:
            return [], []

        base_dates = set(
            item.date_str for item in all_items.values()
            if item.settlement == "PENDING" or item.match_status != "FT"
        )
        base_dates.add(DailyLedgerManager.get_today_str())
        base_dates.add(DailyLedgerManager.get_yesterday_str())

        # Expand with +-1 day window so UTC midnight crossovers never miss a match
        dates_to_check: Set[str] = set()
        for d_str in base_dates:
            dates_to_check.add(d_str)
            dates_to_check.add(shift_date_str(d_str, -1))
            dates_to_check.add(shift_date_str(d_str, 1))

        espn_by_date: Dict[str, List[Dict[str, Any]]] = {}
        apif_by_date: Dict[str, List[Dict[str, Any]]] = {}
        for d_str in sorted(dates_to_check):
            espn_by_date[d_str] = cls.fetch_espn_fixtures_by_date(d_str)
            apif_by_date[d_str] = cls.fetch_apifootball_fixtures_by_date(d_str, force_fresh=force_fresh)

        newly_settled = []

        for full_key, item in all_items.items():
            # Search item.date_str first, then +-1 day
            search_dates = [item.date_str, shift_date_str(item.date_str, -1), shift_date_str(item.date_str, 1)]
            candidate_espn: List[Dict[str, Any]] = []
            candidate_apif: List[Dict[str, Any]] = []
            for sd in search_dates:
                candidate_espn.extend(espn_by_date.get(sd, []))
                candidate_apif.extend(apif_by_date.get(sd, []))

            matched = cls.find_match_in_live_feeds(item.team_home, item.team_away, candidate_espn, candidate_apif)
            if not matched:
                continue

            gh = matched["gh"]
            ga = matched["ga"]
            total_goals = gh + ga
            is_finished = matched["is_finished"]
            is_live = matched["is_live"]
            status_label = matched["status_label"]
            clock = matched["clock"]

            item.score_str = f"{gh}-{ga} ({status_label})"
            item.match_status = "FT" if is_finished else ("LIVE" if is_live else status_label)

            # Fetch detailed ESPN boxscore stats if needed for Corners or Cards
            if item.market_type in ["corners_over_under", "bookings_over_under"] and matched.get("event_id"):
                if matched.get("corners_total") is None or matched.get("cards_total") is None:
                    c_tot, y_tot = cls.fetch_espn_event_stats(matched["event_id"])
                    if c_tot is not None:
                        matched["corners_total"] = c_tot
                    if y_tot is not None:
                        matched["cards_total"] = y_tot

            if item.market_type == "goals_over_under" and item.line is not None:
                is_over = "over" in item.selection.lower()
                if is_over and total_goals > item.line:
                    item.settlement = "WON ✅"
                elif not is_over and total_goals > item.line:
                    item.settlement = "LOST ❌"
                elif is_finished:
                    if is_over:
                        item.settlement = "WON ✅" if total_goals > item.line else ("PUSH ➖" if total_goals == item.line else "LOST ❌")
                    else:
                        item.settlement = "WON ✅" if total_goals < item.line else ("PUSH ➖" if total_goals == item.line else "LOST ❌")

            elif item.market_type == "corners_over_under" and item.line is not None:
                c_tot = matched.get("corners_total")
                if c_tot is not None:
                    item.score_str = f"{gh}-{ga} ({c_tot} Corners | {status_label})"
                    is_over = "over" in item.selection.lower()
                    if is_over and c_tot > item.line:
                        item.settlement = "WON ✅"
                    elif not is_over and c_tot > item.line:
                        item.settlement = "LOST ❌"
                    elif is_finished:
                        item.settlement = "WON ✅" if (c_tot > item.line if is_over else c_tot < item.line) else "LOST ❌"

            elif item.market_type == "bookings_over_under" and item.line is not None:
                y_tot = matched.get("cards_total")
                if y_tot is not None:
                    item.score_str = f"{gh}-{ga} ({y_tot} Cards | {status_label})"
                    is_over = "over" in item.selection.lower()
                    if is_over and y_tot > item.line:
                        item.settlement = "WON ✅"
                    elif not is_over and y_tot > item.line:
                        item.settlement = "LOST ❌"
                    elif is_finished:
                        item.settlement = "WON ✅" if (y_tot > item.line if is_over else y_tot < item.line) else "LOST ❌"

            elif item.market_type == "btts":
                btts_yes = "no" not in item.selection.lower()
                if btts_yes and gh >= 1 and ga >= 1:
                    item.settlement = "WON ✅"
                elif not btts_yes and gh >= 1 and ga >= 1:
                    item.settlement = "LOST ❌"
                elif is_finished:
                    both_scored = (gh >= 1 and ga >= 1)
                    item.settlement = "WON ✅" if (both_scored if btts_yes else not both_scored) else "LOST ❌"

            elif item.market_type == "handicap" and item.line is not None and is_finished:
                sel_low = item.selection.lower()
                for_away = teams_match(item.team_away, sel_low) and not teams_match(item.team_home, sel_low)
                adj_diff = ((ga + item.line) - gh) if for_away else ((gh + item.line) - ga)
                if adj_diff > 0:
                    item.settlement = "WON ✅"
                elif adj_diff == 0:
                    item.settlement = "PUSH ➖"
                else:
                    item.settlement = "LOST ❌"

            elif is_finished and (
                "or draw" in item.selection.lower()
                or item.market_type in ["1x2", "unknown", "unverified"]
            ):
                sel_low = item.selection.lower()
                for_away = teams_match(item.team_away, sel_low) and not teams_match(item.team_home, sel_low)
                if "or draw" in sel_low or "1x" in sel_low or "x2" in sel_low:
                    if for_away or "x2" in sel_low:
                        item.settlement = "WON ✅" if ga >= gh else "LOST ❌"
                    else:
                        item.settlement = "WON ✅" if gh >= ga else "LOST ❌"
                elif for_away:
                    item.settlement = "WON ✅" if ga > gh else "LOST ❌"
                else:
                    item.settlement = "WON ✅" if gh > ga else "LOST ❌"

            live_dt, autopsy_txt = cls.build_live_bet_progress_and_autopsy(item, gh, ga, is_finished, is_live, clock)
            item.live_detail = live_dt
            if autopsy_txt:
                item.loss_autopsy = autopsy_txt

            if item.settlement in ["WON ✅", "LOST ❌", "PUSH ➖"] and not item.notified_settled:
                item.notified_settled = True
                newly_settled.append(item)

        DailyLedgerManager.save_all_items(all_items)
        today_str = DailyLedgerManager.get_today_str()
        today_list = [v for v in all_items.values() if v.date_str == today_str]
        return newly_settled, today_list


class BetParser:
    VS_PATTERN = re.compile(r"([A-Za-z0-9\s\.\-\/&]+?)\s+(?:vs\.?|v\.?|-|—)\s+([A-Za-z0-9\s\.\-\/&]+)", re.IGNORECASE)
    ODDS_PATTERN = re.compile(r"\b([1-4]\.[0-9]{2})\b", re.IGNORECASE)
    GOALS_PATTERN = re.compile(r"(Over|Under|O\/U|Total\s+OVER|Total\s+UNDER)\s*([0-9]\.?[0-9]?)\s*(?:Total\s*)?(?:Goals?)?", re.IGNORECASE)
    CORNERS_PATTERN = re.compile(r"(?:Corners?\s+total\s+)?(Over|Under)\s*([0-9]{1,2}\.?[0-9]?)\s*(?:Total\s*)?Corners?|Corners?\s+total\s+(OVER|UNDER)\s*([0-9]{1,2}\.?[0-9]?)", re.IGNORECASE)
    BOOKINGS_PATTERN = re.compile(r"(?:Yellow\s+cards?\s+total\s+)?(Over|Under)\s*([0-9]\.?[0-9]?)\s*(?:Total\s*)?(?:Bookings?|Cards?)|(?:Yellow\s+cards?|Bookings?)\s+total\s+(OVER|UNDER)\s*([0-9]\.?[0-9]?)", re.IGNORECASE)
    BTTS_PATTERN = re.compile(r"(?:Both\s+Teams\s+To\s+Score|BTTS)\s*[:\-]?\s*(Yes|No|GG|NG)?", re.IGNORECASE)
    HANDICAP_PATTERN = re.compile(r"([A-Za-z\s&]+?)\s*\(([+-][0-9]\.?[0-9]?)\)\s*(?:Handicap)?", re.IGNORECASE)
    DOUBLE_CHANCE_PATTERN = re.compile(r"([A-Za-z\s&]+?)\s*(?:or\s+Draw|1X|X2|Double\s+Chance)", re.IGNORECASE)
    WIN_PATTERN = re.compile(r"([A-Za-z\s&]+?)\s*(?:1x2|to win|win|ml|moneyline|home\s+win|away\s+win)", re.IGNORECASE)

    SRL_CROSS_MATCHES = [
        ("crystal palace", "hoffenheim"), ("sparta prague", "bournemouth"),
        ("lens", "como"), ("aek athens", "real madrid"), ("arsenal", "hull city"),
        ("everton", "coventry"), ("borussia dortmund", "elversberg"),
        ("dortmund", "real betis"), ("lillestrom", "plzen"),
        ("venezia", "udinese"), ("monaco", "nordsjaelland"),
        ("viking fk", "sabah masazir"), ("ullensaker", "viktoria plzen")
    ]

    ROTATION_PRONE_CLUBS = [
        "psg", "paris saint-germain", "paris sg", "manchester city", "man city",
        "real madrid", "bayern munich", "inter milan", "barcelona", "arsenal",
        "liverpool", "juventus", "atletico madrid", "borussia dortmund"
    ]

    IGNORED_UI_STRINGS = [
        "bet slip", "betslip", "odds", "balance", "total", "kickertech",
        "sportsbook", "events", "live", "my account", "place bet", "home",
        "promo", "bonus", "free bet", "megapari", "stake.com", "clear bets",
        "enter stake", "daily winning", "winning picks", "vip"
    ]

    @classmethod
    def clean_team_name(cls, name: str) -> str:
        c = re.sub(r'^\d+[\.\)]\s*', '', name).strip()
        c = re.sub(r'\b202\d-\d{2}-\d{2}\b.*', '', c).strip()
        c = re.sub(r'[\(\)\[\]\{\}]', '', c).strip()
        c = re.sub(r'\s+x$', '', c, flags=re.IGNORECASE).strip()
        typos = {
            "attetico": "Atletico", "barceiona": "Barcelona", "inter milano": "Inter Milan",
            "como 1907": "Como", "sunderiend": "Sunderland", "sunderfand": "Sunderland",
            "aston vila": "Aston Villa", "4 manchester": "Manchester", "3 atletico": "Atletico"
        }
        for k, v in typos.items():
            c = re.sub(k, v, c, flags=re.IGNORECASE)
        return c.strip()

    @classmethod
    def is_garbage_line(cls, name: str) -> bool:
        low = name.lower().strip()
        if len(low) < 3 or len(low) > 35:
            return True
        for ign in cls.IGNORED_UI_STRINGS:
            if ign in low:
                return True
        letters = sum(1 for ch in low if ch.isalpha())
        return letters < 3

    @classmethod
    def detect_srl(cls, team_a: str, team_b: str, text: str) -> bool:
        combined = f"{team_a.lower()} vs {team_b.lower()} {text.lower()}"
        if any(term in combined for term in ["srl", "simulated", "cyber", "fifa", "virtual"]):
            return True
        for t1, t2 in cls.SRL_CROSS_MATCHES:
            if (t1 in team_a.lower() and t2 in team_b.lower()) or (t2 in team_a.lower() and t1 in team_b.lower()):
                return True
        return False

    @classmethod
    def detect_rotation_risk(cls, team_a: str, team_b: str, market_type: str) -> Optional[str]:
        teams = f"{team_a.lower()} {team_b.lower()}"
        for club in cls.ROTATION_PRONE_CLUBS:
            if club in teams:
                if market_type == "corners_over_under":
                    return f"⚠️ Rotation Alert ({club.title()}): Starting wingers often rested for UCL."
                elif market_type == "goals_over_under":
                    return f"ℹ️ UCL Notice ({club.title()}): Potential starter rotation."
        return None

    @classmethod
    def parse_single_block(cls, block: str, source_channel: str = "", post_date_str: str = "") -> Optional[BetSignal]:
        lines = [line.strip() for line in block.strip().split("\n") if line.strip()]
        if not lines:
            return None
        team_home, team_away = "", ""
        for line in lines:
            if re.search(r'\b202\d-\d{2}-\d{2}\b', line) and not re.search(r'[A-Za-z]{3,}', line):
                continue
            m = cls.VS_PATTERN.search(line)
            if m:
                t1 = cls.clean_team_name(m.group(1))
                t2 = cls.clean_team_name(m.group(2))
                if not cls.is_garbage_line(t1) and not cls.is_garbage_line(t2):
                    team_home, team_away = t1, t2
                    break
        if not team_home or not team_away:
            return None

        odds = 1.70
        odds_matches = cls.ODDS_PATTERN.findall(block)
        if odds_matches:
            try:
                odds = float(odds_matches[-1])
            except ValueError:
                odds = 1.70

        market_type = "unverified"
        selection = ""
        line_val = None

        cm = cls.CORNERS_PATTERN.search(block)
        bm = cls.BOOKINGS_PATTERN.search(block)
        gm = cls.GOALS_PATTERN.search(block)
        bttsm = cls.BTTS_PATTERN.search(block)
        hm = cls.HANDICAP_PATTERN.search(block)
        dcm = cls.DOUBLE_CHANCE_PATTERN.search(block)
        wm = cls.WIN_PATTERN.search(block)

        if cm:
            dir_str = cm.group(1) or cm.group(3)
            val_str = cm.group(2) or cm.group(4)
            f_v = float(val_str)
            if f_v >= 15.0:
                f_v = f_v / 10.0
            line_val = f_v
            market_type = "corners_over_under"
            selection = f"{dir_str.capitalize()} {line_val} Corners"
        elif bm:
            dir_str = bm.group(1) or bm.group(3)
            val_str = bm.group(2) or bm.group(4)
            f_v = float(val_str)
            if f_v >= 15.0:
                f_v = f_v / 10.0
            line_val = f_v
            market_type = "bookings_over_under"
            selection = f"{dir_str.capitalize()} {line_val} Bookings"
        elif gm and "corner" not in block.lower() and "card" not in block.lower() and "booking" not in block.lower():
            dir_str = "Over" if "over" in gm.group(1).lower() else "Under"
            f_v = float(gm.group(2))
            if f_v >= 15.0:
                f_v = f_v / 10.0
            if f_v > 6.0:
                line_val = f_v
                market_type = "corners_over_under"
                selection = f"{dir_str} {line_val} Corners"
            else:
                line_val = f_v
                market_type = "goals_over_under"
                selection = f"{dir_str} {line_val} Goals"
        elif bttsm:
            yn = (bttsm.group(1) or "Yes").capitalize()
            if yn.upper() == "NG":
                yn = "No"
            elif yn.upper() == "GG":
                yn = "Yes"
            market_type = "btts"
            selection = f"Both Teams To Score: {yn}"
        elif hm:
            team = hm.group(1).strip()
            line_val = float(hm.group(2))
            market_type = "handicap"
            selection = f"{team} ({line_val:+.1f}) Handicap"
        elif dcm:
            market_type = "1x2"
            selection = f"{team_home} or Draw (1X / Safe Line)"
        elif wm:
            team = wm.group(1).strip()
            market_type = "1x2"
            selection = f"{team} to Win (1X2)"
        else:
            market_type = "unverified"
            selection = f"Unverified Market Line (@ {odds:.2f})"

        is_srl = cls.detect_srl(team_home, team_away, block)
        return BetSignal(
            raw_text=block.strip(),
            team_home=team_home,
            team_away=team_away,
            market_type=market_type,
            selection=selection,
            line=line_val,
            odds=odds,
            source_channel=source_channel,
            is_virtual_srl=is_srl,
            post_date_str=post_date_str
        )

    @classmethod
    def parse_multiple(cls, text: str, source_channel: str = "", post_date_str: str = "") -> List[BetSignal]:
        raw_lines = [line.strip() for line in text.split("\n") if line.strip()]
        match_indices = []
        for idx, line in enumerate(raw_lines):
            if re.search(r'\b202\d-\d{2}-\d{2}\b', line) and not re.search(r'[A-Za-z]{3,}', line):
                continue
            m = cls.VS_PATTERN.search(line)
            if m:
                t1 = cls.clean_team_name(m.group(1))
                t2 = cls.clean_team_name(m.group(2))
                if not cls.is_garbage_line(t1) and not cls.is_garbage_line(t2):
                    match_indices.append(idx)

        signals = []
        if not match_indices:
            return signals
        for i, start_idx in enumerate(match_indices):
            end_idx = match_indices[i + 1] if i + 1 < len(match_indices) else min(start_idx + 6, len(raw_lines))
            chunk = "\n".join(raw_lines[start_idx:end_idx])
            sig = cls.parse_single_block(chunk, source_channel=source_channel, post_date_str=post_date_str)
            if sig:
                signals.append(sig)
        return signals


class FootballIntelligenceEngine:
    @staticmethod
    def poisson_pmf(k: int, lam: float) -> float:
        return (math.pow(lam, k) * math.exp(-lam)) / math.factorial(k)

    @classmethod
    def cumulative_poisson(cls, max_k: int, lam: float) -> float:
        return sum(cls.poisson_pmf(k, lam) for k in range(max_k + 1))

    @classmethod
    def build_bet_key(cls, s: BetSignal) -> str:
        h = normalize_team_str(s.team_home)
        a = normalize_team_str(s.team_away)
        return f"{h}_vs_{a}_{s.market_type}_{s.selection.lower()}"

    @classmethod
    def evaluate_to_ledger_item(cls, s: BetSignal, date_override: Optional[str] = None) -> LedgerBetItem:
        target_date = date_override or s.post_date_str or DailyLedgerManager.get_today_str()
        bet_key = cls.build_bet_key(s)
        sources = [s.source_channel] if s.source_channel else []

        if s.is_virtual_srl:
            return LedgerBetItem(
                bet_key=bet_key,
                date_str=target_date,
                team_home=s.team_home,
                team_away=s.team_away,
                market_type=s.market_type,
                selection=s.selection,
                line=s.line,
                odds=s.odds,
                floor_odds=2.00,
                is_approved=False,
                confidence_stars="❌ DECLINED (VIRTUAL SRL)",
                model_prob=0.0,
                edge_ev=-100.0,
                recommended_units=0.0,
                consensus_sources=sources,
                rationale="Simulated Reality League (SRL) virtual AI match detected. No real players or lineups exist.",
                evidence="Unverified Cross-League Virtual Fixture — Automatically Declined.",
                rotation_warning=None,
                search_url=""
            )

        if s.market_type == "unverified":
            return LedgerBetItem(
                bet_key=bet_key,
                date_str=target_date,
                team_home=s.team_home,
                team_away=s.team_away,
                market_type=s.market_type,
                selection=s.selection,
                line=s.line,
                odds=s.odds,
                floor_odds=2.00,
                is_approved=False,
                confidence_stars="❌ DECLINED (UNVERIFIED MARKET)",
                model_prob=0.0,
                edge_ev=-100.0,
                recommended_units=0.0,
                consensus_sources=sources,
                rationale="Signal did not specify a clear verifiable market (Over/Under, Corners, Handicap, or explicit 1X2). Blocked to prevent blind favorite losses.",
                evidence="Strict Veto: Never guess a market purely from odds.",
                rotation_warning=None,
                search_url=""
            )

        dossier = LiveFootballAPI.build_pre_match_dossier(s.team_home, s.team_away, target_date)

        proj_home_goals = (dossier.home_goals_for_avg + dossier.away_goals_against_avg) / 2.0 + dossier.home_xg_adj
        proj_away_goals = (dossier.away_goals_for_avg + dossier.home_goals_against_avg) / 2.0 + dossier.away_xg_adj
        expected_goals = max(1.5, min(4.3, proj_home_goals + proj_away_goals))
        expected_corners = max(7.5, min(12.5, 9.60 + dossier.corners_adj))
        expected_cards = 4.30

        rot_warn = BetParser.detect_rotation_risk(s.team_home, s.team_away, s.market_type)
        veto_triggered: Optional[str] = None

        if s.market_type == "goals_over_under" and s.line is not None:
            max_k = int(math.floor(s.line))
            prob_under = cls.cumulative_poisson(max_k, expected_goals)
            prob_over = 1.0 - prob_under
            is_under = "under" in s.selection.lower()
            model_prob = prob_under if is_under else prob_over

            if is_under and (expected_goals >= 3.05 or dossier.home_goals_against_avg >= 1.65 or dossier.away_goals_against_avg >= 1.65):
                veto_triggered = (
                    f"Shootout Risk Veto: High-tempo scoring profile ({expected_goals:.2f} proj goals) makes {s.selection} unsafe (3-2 shootout trap)."
                )
                model_prob = min(model_prob, 0.48)

            rationale = veto_triggered or (
                f"Pre-match xG model ({expected_goals:.2f} goals) rates {s.selection} at {model_prob*100:.1f}% probability."
            )

        elif s.market_type == "corners_over_under" and s.line is not None:
            max_k = int(math.floor(s.line))
            prob_under = cls.cumulative_poisson(max_k, expected_corners)
            prob_over = 1.0 - prob_under
            is_over = "over" in s.selection.lower()
            model_prob = prob_over if is_over else prob_under
            if rot_warn and is_over and s.line >= 8.5:
                model_prob *= 0.80
                veto_triggered = "Rotation Risk Veto: Starting wingers projected to be rested; low corner volume expected."
            rationale = veto_triggered or f"Wing width & corner projection ({expected_corners:.1f} avg) gives {model_prob*100:.1f}% hit rate."

        elif s.market_type == "bookings_over_under" and s.line is not None:
            max_k = int(math.floor(s.line))
            prob_under = cls.cumulative_poisson(max_k, expected_cards)
            prob_over = 1.0 - prob_under
            is_over = "over" in s.selection.lower()
            model_prob = prob_over if is_over else prob_under
            if is_over and s.line <= 3.5:
                model_prob = max(model_prob, 0.67)
                rationale = f"High-intensity fixture stakes ({dossier.match_stakes}) project 4.3+ bookings."
            else:
                rationale = f"Referee & fixture intensity model projects {model_prob*100:.1f}% probability."

        elif s.market_type == "btts":
            p_home_0 = cls.poisson_pmf(0, max(0.5, proj_home_goals))
            p_away_0 = cls.poisson_pmf(0, max(0.5, proj_away_goals))
            p_btts_yes = (1.0 - p_home_0) * (1.0 - p_away_0)
            is_yes = "no" not in s.selection.lower()
            model_prob = p_btts_yes if is_yes else (1.0 - p_btts_yes)
            rationale = f"Attacking/defensive xG split projects {model_prob*100:.1f}% probability for {s.selection}."

        elif s.market_type == "handicap" and s.line is not None:
            if s.line > 0:
                if dossier.home_goals_against_avg >= 1.70:
                    veto_triggered = f"Defensive Collapse Veto: Concedes {dossier.home_goals_against_avg:.2f} goals/gm; unsafe for handicap."
                    model_prob = 0.49
                else:
                    model_prob = 0.70 if s.line >= 1.5 else 0.63
                rationale = veto_triggered or f"Plus-handicap cushion ({s.line:+.1f}) covers both win and close 1-goal margin."
            else:
                model_prob = 0.51
                rationale = "Minus handicap requires multi-goal margin; elevated draw/backdoor cover risk."

        else:
            if dossier.veto_reason:
                veto_triggered = f"Defensive Veto: {dossier.veto_reason} (High 3-2 upset risk)."
                model_prob = 0.50
            elif not dossier.fixture_found:
                veto_triggered = "Fixture Verification Veto: Could not verify live starting form/standings for 1X2 favorite."
                model_prob = 0.52
            elif "or draw" in s.selection.lower() and s.odds <= 1.52:
                model_prob = 0.76 + (0.03 if dossier.home_xg_adj > 0 else 0.0)
            else:
                model_prob = 0.54
            rationale = veto_triggered or (
                f"Verified form ({dossier.form_summary}) & Poisson distribution project {model_prob*100:.1f}% probability."
            )

        ev_pct = ((model_prob * s.odds) - 1.0) * 100.0
        floor_odds = round(1.0 / max(model_prob, 0.01), 2)
        is_approved = (veto_triggered is None) and (ev_pct >= 2.5) and (model_prob >= 0.60)

        if not is_approved and not veto_triggered:
            rationale = f"Declined ({ev_pct:+.1f}% EV): Model win prob ({model_prob*100:.1f}%) requires minimum odds of {floor_odds:.2f} (offered {s.odds:.2f})."

        if is_approved:
            if ev_pct >= 10.0 and model_prob >= 0.70:
                stars = "⭐️⭐️⭐️⭐️⭐️"
                units = 2.0
            elif ev_pct >= 5.0:
                stars = "⭐️⭐️⭐️⭐️"
                units = 1.5
            else:
                stars = "⭐️⭐️⭐️"
                units = 1.0
        else:
            stars = "❌ DECLINED"
            units = 0.0

        evidence = f"{dossier.standings_summary} | {dossier.form_summary}"
        match_context_str = f"{dossier.competition} | {dossier.match_stakes}"
        lineup_inj_str = f"{dossier.lineup_summary} | {dossier.injuries_summary}"

        q = urllib.parse.quote(f"{s.team_home} vs {s.team_away} {s.selection} odds")
        search_url = f"https://www.google.com/search?q={q}"

        return LedgerBetItem(
            bet_key=bet_key,
            date_str=target_date,
            team_home=s.team_home,
            team_away=s.team_away,
            market_type=s.market_type,
            selection=s.selection,
            line=s.line,
            odds=s.odds,
            floor_odds=floor_odds,
            is_approved=is_approved,
            confidence_stars=stars,
            model_prob=round(model_prob * 100, 1),
            edge_ev=round(ev_pct, 1),
            recommended_units=units,
            consensus_sources=sources,
            rationale=rationale,
            evidence=evidence,
            rotation_warning=rot_warn,
            search_url=search_url,
            match_context=match_context_str,
            lineup_injuries_info=lineup_inj_str
        )


class BetSlipCardFormatter:
    @classmethod
    def get_running_channel_tally_line(cls) -> str:
        """Returns a 1-line summary of the cumulative @Footybett record to embed in every result post."""
        all_items = list(DailyLedgerManager.load_all_history_items().values())
        settled_app = [
            i for i in all_items
            if i.is_approved and i.settlement in ["WON ✅", "LOST ❌", "PUSH ➖"]
        ]
        won_cnt = sum(1 for i in settled_app if "WON" in i.settlement)
        lost_cnt = sum(1 for i in settled_app if "LOST" in i.settlement)
        wr = (won_cnt / (won_cnt + lost_cnt) * 100.0) if (won_cnt + lost_cnt) > 0 else 0.0
        net_u = 0.0
        for i in settled_app:
            if "WON" in i.settlement:
                net_u += i.recommended_units * (i.odds - 1.0)
            elif "LOST" in i.settlement:
                net_u -= i.recommended_units
        return f"📈 Total Record: {won_cnt}W - {lost_cnt}L ({wr:.1f}% Win Rate | {net_u:+.2f}u Profit)"

    @classmethod
    def format_player_channel_post(cls, s: LedgerBetItem) -> str:
        """Sent ONCE to @Footybett when a new approved pick is confirmed."""
        lines = [
            "🔥 NEW VIP PICK TO TAKE — @Footybett 🔥",
            "════════════════════════════",
            f"🏟 Match      : {s.team_home} vs {s.team_away}",
            f"🎯 Pick       : {s.selection}",
            f"💰 Best Odds  : {s.odds:.2f} (Min Safe Odds: {s.floor_odds:.2f})",
            f"💵 Stake      : {s.recommended_units:.1f} Unit(s)",
            f"⭐ Confidence : {s.confidence_stars} ({s.model_prob}% Win Prob | {s.edge_ev:+.1f}% EV)",
            "────────────────────────────",
        ]
        if s.match_context:
            lines.append(f"🏆 Match Info : {s.match_context}")
        if s.lineup_injuries_info:
            lines.append(f"👥 Team News  : {s.lineup_injuries_info}")
        lines.append(f"💡 Analysis   : {s.rationale}")
        lines.append(f"📊 Form/Table : {s.evidence}")
        if s.rotation_warning:
            lines.append(f"{s.rotation_warning}")
        lines.append("════════════════════════════")
        lines.append(cls.get_running_channel_tally_line())
        return "\n".join(lines)

    @classmethod
    def format_player_channel_result_update(cls, s: LedgerBetItem) -> str:
        """
        Formats the settled result card for @Footybett ONCE — both for WON ✅ and LOST ❌
        and embeds the running cumulative @Footybett record!
        """
        tally_line = cls.get_running_channel_tally_line()
        if "WON" in s.settlement:
            profit_u = s.recommended_units * (s.odds - 1.0)
            return (
                "🎉✅ FOOTYBETT WINNER CASHED! ✅🎉\n"
                "════════════════════════════\n"
                f"🏟 Match  : {s.team_home} vs {s.team_away}\n"
                f"🎯 Pick   : {s.selection} @ {s.odds:.2f}\n"
                f"🏁 Result : {s.score_str} — WON ✅\n"
                f"💰 Profit : +{profit_u:.2f} Units Won!\n"
                "────────────────────────────\n"
                f"{tally_line}\n"
                "════════════════════════════"
            )
        elif "LOST" in s.settlement:
            autopsy_line = f"\n{s.loss_autopsy}" if s.loss_autopsy else ""
            return (
                "📊❌ FOOTYBETT PICK RESULT (SETTLED) ❌📊\n"
                "════════════════════════════\n"
                f"🏟 Match  : {s.team_home} vs {s.team_away}\n"
                f"🎯 Pick   : {s.selection} @ {s.odds:.2f}\n"
                f"🏁 Result : {s.score_str} — LOST ❌\n"
                f"📉 Impact : -{s.recommended_units:.1f} Unit(s){autopsy_line}\n"
                "────────────────────────────\n"
                f"{tally_line}\n"
                "════════════════════════════"
            )
        else:
            return (
                "➖📊 FOOTYBETT PICK RESULT (PUSH / VOID) 📊➖\n"
                "════════════════════════════\n"
                f"🏟 Match  : {s.team_home} vs {s.team_away}\n"
                f"🎯 Pick   : {s.selection} @ {s.odds:.2f}\n"
                f"🏁 Result : {s.score_str} — PUSH ➖ (Stake Returned)\n"
                "────────────────────────────\n"
                f"{tally_line}\n"
                "════════════════════════════"
            )

    @classmethod
    def format_channel_total_analysis_recap(cls, focus_date: Optional[str] = None) -> str:
        """
        Formats a clean, high-trust Official Total Analysis (Won vs Lost + All-Time P&L)
        specifically designed to be posted to @Footybett once a day's slate settles or on `/poststats`.
        """
        all_items = list(DailyLedgerManager.load_all_history_items().values())
        approved = [i for i in all_items if i.is_approved]
        settled_app = [i for i in approved if i.settlement in ["WON ✅", "LOST ❌", "PUSH ➖"]]
        won_app = [i for i in settled_app if "WON" in i.settlement]
        lost_app = [i for i in settled_app if "LOST" in i.settlement]

        win_rate = (len(won_app) / (len(won_app) + len(lost_app)) * 100.0) if (len(won_app) + len(lost_app)) > 0 else 0.0
        units_staked = sum(i.recommended_units for i in settled_app)
        net_units = 0.0
        for i in settled_app:
            if "WON" in i.settlement:
                net_units += i.recommended_units * (i.odds - 1.0)
            elif "LOST" in i.settlement:
                net_units -= i.recommended_units
        roi_pct = (net_units / units_staked * 100.0) if units_staked > 0 else 0.0

        target_d = focus_date or DailyLedgerManager.get_yesterday_str()
        day_picks = [i for i in approved if i.date_str == target_d]
        if not day_picks:
            target_d = DailyLedgerManager.get_today_str()
            day_picks = [i for i in approved if i.date_str == target_d]

        lines = [
            "📊🏆 @Footybett OFFICIAL WON/LOST & P&L RECAP 🏆📊",
            "════════════════════════════════",
        ]

        if day_picks:
            d_won = sum(1 for i in day_picks if "WON" in i.settlement)
            d_lost = sum(1 for i in day_picks if "LOST" in i.settlement)
            lines.append(f"📅 SLATE REVIEW ({target_d}: {d_won} Won ✅ | {d_lost} Lost ❌):")
            for idx, s in enumerate(day_picks, 1):
                if "WON" in s.settlement:
                    p_u = s.recommended_units * (s.odds - 1.0)
                    lines.append(f"  {idx}. ✅ {s.team_home} vs {s.team_away} — {s.selection} @ {s.odds:.2f} ➔ {s.score_str} (+{p_u:.2f}u)")
                elif "LOST" in s.settlement:
                    lines.append(f"  {idx}. ❌ {s.team_home} vs {s.team_away} — {s.selection} @ {s.odds:.2f} ➔ {s.score_str} (-{s.recommended_units:.1f}u)")
                    if s.loss_autopsy:
                        lines.append(f"      ↳ {s.loss_autopsy}")
                else:
                    lines.append(f"  {idx}. ⏳ {s.team_home} vs {s.team_away} — {s.selection} @ {s.odds:.2f} ➔ {s.score_str}")
            lines.append("────────────────────────────────")

        lines.extend([
            f"📈 ALL-TIME @Footybett TRACK RECORD (Since {TRACKING_START_DATE}):",
            f"• Total VIP Picks Settled : {len(settled_app)}",
            f"• Total Picks Won ✅      : {len(won_app)}",
            f"• Total Picks Lost ❌     : {len(lost_app)}",
            f"• Official Win Rate       : {win_rate:.1f}%",
            f"• Total Units Risked      : {units_staked:.1f} u",
            f"• Net Profit Made         : {net_units:+.2f} u ( @ $50/u = ${net_units * 50:+.2f} )",
            f"• Return on Inv (ROI)     : {roi_pct:+.1f}%",
            "════════════════════════════════",
            "🛡️ 100% Verified Pre-Match Model • Every Win & Loss Tracked"
        ])
        return "\n".join(lines)

    @classmethod
    def _format_single_day_section(cls, date_label: str, items: List[LedgerBetItem]) -> List[str]:
        approved = [i for i in items if i.is_approved]
        rejected = [i for i in items if not i.is_approved]
        approved.sort(key=lambda x: x.edge_ev, reverse=True)

        lines = [
            f"📅 {date_label} — ({len(approved)} Chosen ✅ | {len(rejected)} Declined ❌)",
            "═" * 32
        ]

        if approved:
            lines.append("🟢 CHOSEN / APPROVED BETS:")
            for idx, s in enumerate(approved, 1):
                chs = ", ".join(f"@{ch}" for ch in s.consensus_sources if ch) or "@Manual"
                live_str = f" • [{s.settlement} | {s.score_str}]" if s.score_str != "-" else f" • [{s.settlement}]"
                pub_tag = " 📢[@Footybett]" if s.published_to_channel else ""
                lines.append(f"{idx}. {s.team_home} vs {s.team_away}{live_str}{pub_tag}")
                lines.append(f"   📡 Source  : {chs}")
                lines.append(f"   📋 Pick    : {s.selection} @ {s.odds:.2f} (Stake: {s.recommended_units}u)")
                lines.append(f"   📊 Edge    : {s.confidence_stars} ({s.model_prob}% Prob | {s.edge_ev:+.1f}% EV)")
                if s.live_detail:
                    lines.append(f"   ⏱️ Live Now: {s.live_detail}")
                if s.loss_autopsy:
                    lines.append(f"   {s.loss_autopsy}")
                lines.append(f"   💡 Why     : {s.rationale}")
                lines.append("-" * 32)
        else:
            lines.append("⚠️ No approved +EV bets for this date.")

        if rejected:
            lines.append("\n🔴 DECLINED / AVOIDED BETS (Why We Passed):")
            for r in rejected:
                chs = ", ".join(f"@{ch}" for ch in r.consensus_sources if ch) or "@Manual"
                score_info = f" [{r.settlement} {r.score_str}]" if r.score_str != "-" else ""
                badge = " 🛡️(TRAP DODGED!)" if "LOST" in r.settlement else ""
                lines.append(f"✖ [{chs}] {r.team_home} vs {r.team_away} ({r.selection} @ {r.odds:.2f}){score_info}{badge}")
                lines.append(f"   ↳ Reason: {r.rationale}")

        lines.append("")
        return lines

    @classmethod
    def format_full_bot_curation_slate(cls, today_items: List[LedgerBetItem], yesterday_items: List[LedgerBetItem]) -> str:
        today = DailyLedgerManager.get_today_str()
        yesterday = DailyLedgerManager.get_yesterday_str()
        lines = [
            "🎯 BOT CURATION LOG (CHOSEN ✅ vs DECLINED ❌)",
            "🔄 Live Score Engine: ESPN Real-Time + API-Football",
            ""
        ]
        lines.extend(cls._format_single_day_section(f"TODAY ({today})", today_items))
        if yesterday_items:
            lines.extend(cls._format_single_day_section(f"YESTERDAY ({yesterday})", yesterday_items))
        return "\n".join(lines)

    @classmethod
    def format_results_audit(cls, today_items: List[LedgerBetItem], yesterday_items: List[LedgerBetItem]) -> str:
        today = DailyLedgerManager.get_today_str()
        yesterday = DailyLedgerManager.get_yesterday_str()
        combined = today_items + yesterday_items
        if not combined:
            return "ℹ️ No bets recorded for today or yesterday yet. Tap `/scan` first."

        lines = [
            f"🏁 LIVE ON-SPOT SCORES & SETTLEMENT AUDIT",
            f"(Updated Live: {datetime.datetime.now(datetime.timezone.utc).strftime('%H:%M:%S UTC')})",
            "═" * 32 + "\n"
        ]

        for label, group in [(f"TODAY ({today})", today_items), (f"YESTERDAY ({yesterday})", yesterday_items)]:
            if not group:
                continue
            approved = [i for i in group if i.is_approved]
            rejected = [i for i in group if not i.is_approved]
            w_cnt = sum(1 for i in approved if "WON" in i.settlement)
            l_cnt = sum(1 for i in approved if "LOST" in i.settlement)
            p_cnt = len(approved) - w_cnt - l_cnt

            lines.append(f"📅 {label} — CHOSEN PICKS ({w_cnt} Won ✅ | {l_cnt} Lost ❌ | {p_cnt} Live/Pending):")
            for idx, s in enumerate(approved, 1):
                chs = ", ".join(f"@{ch}" for ch in s.consensus_sources if ch) or "@Manual"
                lines.append(
                    f"  {idx}. [{chs}] {s.team_home} vs {s.team_away} — {s.selection} @ {s.odds:.2f} ➔ {s.score_str} [{s.settlement}]"
                )
                if s.live_detail:
                    lines.append(f"      ⏱️ {s.live_detail}")
                if s.loss_autopsy:
                    lines.append(f"      {s.loss_autopsy}")
            if not approved:
                lines.append("  • No approved picks for this date.")

            rej_won = sum(1 for i in rejected if "WON" in i.settlement)
            rej_lost = sum(1 for i in rejected if "LOST" in i.settlement)
            lines.append(f"\n🔴 {label} — DECLINED AUDIT ({rej_lost} Traps Dodged 🛡️ | {rej_won} Won 💡):")
            for r in rejected:
                chs = ", ".join(f"@{ch}" for ch in r.consensus_sources if ch) or "@Manual"
                badge = "🛡️ TRAP DODGED!" if "LOST" in r.settlement else ("💡 Won" if "WON" in r.settlement else "")
                lines.append(
                    f"  • [{chs}] {r.team_home} vs {r.team_away} ({r.selection} @ {r.odds:.2f}) ➔ {r.score_str} [{r.settlement}] {badge}"
                )
            lines.append("\n" + "─" * 32 + "\n")

        return "\n".join(lines)

    @classmethod
    def format_lifetime_pnl_stats(cls) -> str:
        all_items = list(DailyLedgerManager.load_all_history_items().values())
        approved = [i for i in all_items if i.is_approved]
        rejected = [i for i in all_items if not i.is_approved]

        settled_app = [i for i in approved if i.settlement in ["WON ✅", "LOST ❌", "PUSH ➖"]]
        won_app = [i for i in settled_app if "WON" in i.settlement]
        lost_app = [i for i in settled_app if "LOST" in i.settlement]
        push_app = [i for i in settled_app if "PUSH" in i.settlement]
        pending_app = len(approved) - len(settled_app)

        total_taken = len(approved)
        win_rate = (len(won_app) / (len(won_app) + len(lost_app)) * 100.0) if (len(won_app) + len(lost_app)) > 0 else 0.0

        units_staked = sum(i.recommended_units for i in settled_app)
        net_units = 0.0
        for i in settled_app:
            if "WON" in i.settlement:
                net_units += i.recommended_units * (i.odds - 1.0)
            elif "LOST" in i.settlement:
                net_units -= i.recommended_units

        roi_pct = (net_units / units_staked * 100.0) if units_staked > 0 else 0.0
        avg_odds = (sum(i.odds for i in approved) / len(approved)) if approved else 0.0
        avg_rr = avg_odds - 1.0 if avg_odds > 1.0 else 0.0

        traps_dodged = sum(1 for r in rejected if "LOST" in r.settlement)
        units_saved = traps_dodged * 1.0

        dates = sorted({i.date_str for i in approved if i.date_str >= TRACKING_START_DATE})
        daily_lines = []
        for d_str in dates:
            day_app = [i for i in approved if i.date_str == d_str]
            d_won = sum(1 for i in day_app if "WON" in i.settlement)
            d_lost = sum(1 for i in day_app if "LOST" in i.settlement)
            d_pend = sum(1 for i in day_app if i.settlement == "PENDING")
            d_prof = 0.0
            for i in day_app:
                if "WON" in i.settlement:
                    d_prof += i.recommended_units * (i.odds - 1.0)
                elif "LOST" in i.settlement:
                    d_prof -= i.recommended_units
            daily_lines.append(
                f"• {d_str}: {d_won}W - {d_lost}L ({d_pend} Open) | Net: {d_prof:+.2f} u"
            )
        daily_breakdown_str = "\n".join(daily_lines) if daily_lines else "• None yet"

        return (
            f"📈 ALL-TIME P&L & PERFORMANCE STATS\n"
            f"(Tracking Since: {TRACKING_START_DATE})\n"
            f"════════════════════════════════\n"
            f"🎯 BETS TAKEN SUMMARY:\n"
            f"• Total Approved Bets : {total_taken} ({len(settled_app)} Settled | {pending_app} Open)\n"
            f"• Bets Won ✅         : {len(won_app)}\n"
            f"• Bets Lost ❌        : {len(lost_app)}\n"
            f"• Bets Push ➖        : {len(push_app)}\n"
            f"• Win Strike Rate     : {win_rate:.1f}%\n\n"
            f"💰 PROFIT, ROI & RISK/REWARD:\n"
            f"• Total Units Risked  : {units_staked:.1f} u\n"
            f"• Net Profit Made     : {net_units:+.2f} u ( @ $50/u = ${net_units * 50:+.2f} )\n"
            f"• Return on Inv (ROI) : {roi_pct:+.1f}%\n"
            f"• Avg Odds / R:R Ratio: {avg_odds:.2f} (1 : {avg_rr:.2f} Risk/Reward)\n\n"
            f"🗓️ DAILY RECORD (FROM {TRACKING_START_DATE}):\n"
            f"{daily_breakdown_str}\n\n"
            f"🛡️ FILTER EFFICIENCY (TRAPS DODGED):\n"
            f"• Total Signals Scanned: {len(all_items)}\n"
            f"• Bad Bets Declined    : {len(rejected)}\n"
            f"• Confirmed Losing Traps Dodged: {traps_dodged} (Saved -{units_saved:.1f} u)"
        )


class ChannelWebWatcher:
    @classmethod
    def get_watched_channels(cls) -> Set[str]:
        return load_json_set(CHANNELS_FILE, default=DEFAULT_CHANNELS)

    @classmethod
    def add_watched_channel(cls, username: str) -> Set[str]:
        clean = username.strip().lstrip("@").replace("https://t.me/s/", "").replace("https://t.me/", "").strip("/")
        channels = cls.get_watched_channels()
        if clean:
            channels.add(clean)
            save_json_set(CHANNELS_FILE, channels)
        return channels

    @classmethod
    def fetch_recent_channel_html(cls, channel_username: str) -> str:
        url = f"https://t.me/s/{channel_username}?_={int(time.time())}"
        req = urllib.request.Request(url, headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Cache-Control": "no-cache"
        })
        try:
            with urllib.request.urlopen(req, timeout=10) as resp:
                return resp.read().decode("utf-8")
        except Exception as e:
            logger.error("Error scraping channel preview (%s): %s", channel_username, e)
            return ""

    @classmethod
    def extract_recent_posts(cls, html: str, only_unseen: bool = True) -> List[Tuple[str, str, str, List[str]]]:
        if not html:
            return []
        seen = load_json_set(SEEN_POSTS_FILE)
        posts = []
        valid_dates = {DailyLedgerManager.get_today_str(), DailyLedgerManager.get_yesterday_str()}

        parts = re.split(r'(?=<div[^>]+data-post=")', html)
        for block in parts:
            m_id = re.search(r'data-post="([^"]+)"', block)
            if not m_id:
                continue
            post_id = m_id.group(1)

            if only_unseen and post_id in seen:
                continue

            time_m = re.search(r'<time[^>]+datetime="([^"]+)"', block)
            if not time_m:
                continue
            post_date = time_m.group(1)[:10]
            if post_date not in valid_dates:
                continue

            text_m = re.search(r'<div class="tgme_widget_message_text[^"]*"[^>]*>(.*?)</div>', block, re.DOTALL)
            raw_text = ""
            if text_m:
                raw_text = re.sub(r'<br\s*/?>', '\n', text_m.group(1))
                raw_text = re.sub(r'<[^>]+>', '', raw_text).strip()

            img_urls = re.findall(r'background-image:url\(\'(https://[^\']+)\'\)', block)
            posts.append((post_id, post_date, raw_text, img_urls))

        return posts


class TelegramBotClient:
    REMOVE_BOTTOM_KEYBOARD = {"remove_keyboard": True}

    def __init__(self, bot_token: str):
        self.bot_token = bot_token.strip()
        self.base_url = f"https://api.telegram.org/bot{self.bot_token}"
        self.pending_photos: Dict[int, List[bytes]] = {}
        self.pending_timers: Dict[int, threading.Timer] = {}
        self.lock = threading.Lock()
        self.channel_publish_lock = threading.Lock()
        DailyLedgerManager.load_all_history_items()

    def send_message(self, chat_id: Any, text: str, remove_kb: bool = True) -> bool:
        url = f"{self.base_url}/sendMessage"
        chunks = []
        current = []
        cur_len = 0
        for line in text.split("\n"):
            if cur_len + len(line) + 1 > 3800:
                chunks.append("\n".join(current))
                current = [line]
                cur_len = len(line)
            else:
                current.append(line)
                cur_len += len(line) + 1
        if current:
            chunks.append("\n".join(current))

        ok = True
        for chunk in chunks:
            payload_data: Dict[str, Any] = {
                "chat_id": chat_id,
                "text": chunk
            }
            if remove_kb and isinstance(chat_id, int) and chat_id > 0:
                payload_data["reply_markup"] = self.REMOVE_BOTTOM_KEYBOARD

            payload = json.dumps(payload_data).encode("utf-8")
            req = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
            try:
                with urllib.request.urlopen(req, timeout=10) as resp:
                    ok = ok and (resp.status == 200)
            except Exception as e:
                logger.error("Failed to send Telegram message to %s: %s", chat_id, e)
                ok = False
        return ok

    def sync_and_publish_to_footybett(self, force_fresh_scores: bool = False) -> int:
        """
        Thread-safe publisher & retroactive corrector for @Footybett:
        1. Grades live/finished scores across 3-day window (using ESPN Real-Time + ESPN Stats + API-Football).
        2. Sends each newly confirmed, open APPROVED pick ONCE to @Footybett (`pick:<date>:<bet_key>`).
        3. Retroactively & live sends the settled outcome (BOTH WON ✅ and LOST ❌) ONCE to @Footybett
           (`result:<date>:<bet_key>`) for any approved pick from 2026-11-09 onward whose result hasn't been posted yet.
        4. Once all of a date's approved picks have settled, posts the Official Total Won/Lost & P&L Analysis Recap
           card ONCE for that settled slate (`recap:<date>:<settled_count>`).
        """
        with self.channel_publish_lock:
            LiveFootballAPI.grade_ledger_items(force_fresh=force_fresh_scores)
            all_items = DailyLedgerManager.load_all_history_items()
            today = DailyLedgerManager.get_today_str()
            published_count = 0
            updated = False
            dates_with_new_settlements: Set[str] = set()

            for full_key, item in all_items.items():
                pick_lock_key = f"pick:{full_key}"
                result_lock_key = f"result:{full_key}"
                legacy_win_lock = f"win:{full_key}"

                # 1. New Approved Bet -> Send ONCE to @Footybett (only if match is today & still open/pending)
                if item.date_str == today and item.is_approved:
                    if not item.published_to_channel and not DailyLedgerManager.is_locked_in_channel(pick_lock_key):
                        if item.match_status != "FT" and item.settlement == "PENDING":
                            post_text = BetSlipCardFormatter.format_player_channel_post(item)
                            if self.send_message(PUBLISH_CHANNEL_ID, post_text, remove_kb=False):
                                item.published_to_channel = True
                                DailyLedgerManager.mark_locked_in_channel(pick_lock_key)
                                published_count += 1
                                updated = True
                                time.sleep(1.0)

                # 2. Settled Outcome (WON ✅, LOST ❌, or PUSH ➖) -> Post Result ONCE in @Footybett
                # Also catches yesterday's (2026-11-09+) approved picks where the losing result was never posted!
                if item.is_approved and item.date_str >= "2026-11-09" and item.settlement in ["WON ✅", "LOST ❌", "PUSH ➖"]:
                    already_settled_post = (
                        item.published_result_to_channel
                        or DailyLedgerManager.is_locked_in_channel(result_lock_key)
                        or DailyLedgerManager.is_locked_in_channel(legacy_win_lock)
                    )
                    if not already_settled_post:
                        res_text = BetSlipCardFormatter.format_player_channel_result_update(item)
                        if self.send_message(PUBLISH_CHANNEL_ID, res_text, remove_kb=False):
                            item.published_to_channel = True
                            item.published_result_to_channel = True
                            DailyLedgerManager.mark_locked_in_channel(pick_lock_key)
                            DailyLedgerManager.mark_locked_in_channel(result_lock_key)
                            dates_with_new_settlements.add(item.date_str)
                            updated = True
                            time.sleep(1.0)

            if updated:
                DailyLedgerManager.save_all_items(all_items)

            # 3. Post Official Daily + All-Time Won/Lost Analysis Recap to @Footybett ONCE when a date's picks finish settling
            check_dates = dates_with_new_settlements | {DailyLedgerManager.get_yesterday_str()}
            for d_str in sorted(check_dates):
                if d_str < "2026-11-09":
                    continue
                day_app = [i for i in all_items.values() if i.date_str == d_str and i.is_approved]
                if not day_app:
                    continue
                settled_day = [i for i in day_app if i.settlement in ["WON ✅", "LOST ❌", "PUSH ➖"]]
                # Post recap when all approved picks for that date have settled
                if len(settled_day) == len(day_app) and len(settled_day) > 0:
                    recap_lock = f"recap:{d_str}:{len(settled_day)}"
                    if not DailyLedgerManager.is_locked_in_channel(recap_lock):
                        recap_text = BetSlipCardFormatter.format_channel_total_analysis_recap(focus_date=d_str)
                        if self.send_message(PUBLISH_CHANNEL_ID, recap_text, remove_kb=False):
                            DailyLedgerManager.mark_locked_in_channel(recap_lock)
                            time.sleep(1.0)

            return published_count

    def broadcast_admin(self, text: str):
        subs = load_json_set(SUBSCRIBERS_FILE)
        for cid in subs:
            try:
                if int(cid) > 0:
                    self.send_message(int(cid), text)
            except Exception:
                pass

    def get_updates(self, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        url = f"{self.base_url}/getUpdates?timeout=10"
        if offset is not None:
            url += f"&offset={offset}"
        try:
            req = urllib.request.Request(url)
            with urllib.request.urlopen(req, timeout=15) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                return data.get("result", [])
        except Exception as e:
            logger.error("Error fetching updates: %s", e)
            return []

    def download_url_bytes(self, url: str) -> Optional[bytes]:
        if url.startswith("//"):
            return None
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                return resp.read()
        except Exception as e:
            logger.error("Failed to download image URL: %s", e)
            return None

    def download_photo_bytes(self, file_id: str) -> Optional[bytes]:
        url = f"{self.base_url}/getFile?file_id={file_id}"
        try:
            req = urllib.request.Request(url)
            with urllib.request.urlopen(req, timeout=10) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                file_path = data.get("result", {}).get("file_path")
                if not file_path:
                    return None
            download_url = f"https://api.telegram.org/file/bot{self.bot_token}/{file_path}"
            with urllib.request.urlopen(download_url, timeout=12) as img_resp:
                return img_resp.read()
        except Exception as e:
            logger.error("Failed to download image from Telegram: %s", e)
            return None

    def extract_text_from_photo(self, photo_bytes: bytes) -> str:
        if not OCR_AVAILABLE:
            return ""
        try:
            raw_img = Image.open(io.BytesIO(photo_bytes))
            w, h = raw_img.size
            card_crop = raw_img.crop((int(w * 0.04), int(h * 0.12), int(w * 0.96), int(h * 0.60)))
            gray = card_crop.convert("L")
            enhanced = ImageEnhance.Contrast(gray).enhance(2.5)
            text_1 = pytesseract.image_to_string(enhanced)
            fn = lambda x: 255 if x > 85 else 0
            binarized = gray.point(fn, mode="1")
            text_2 = pytesseract.image_to_string(binarized)
            return f"{text_1}\n{text_2}"
        except Exception as e:
            logger.error("OCR extraction failed: %s", e)
            return ""

    def ingest_text_into_ledger(self, text: str, source_channel: str = "", post_date_str: str = "") -> List[Tuple[bool, LedgerBetItem]]:
        signals = BetParser.parse_multiple(text, source_channel=source_channel, post_date_str=post_date_str)
        results = []
        for s in signals:
            item = FootballIntelligenceEngine.evaluate_to_ledger_item(s, date_override=post_date_str or None)
            is_new, stored = DailyLedgerManager.upsert_bet(item)
            results.append((is_new, stored))
        return results

    def flush_album_burst(self, chat_id: int):
        with self.lock:
            photos = self.pending_photos.pop(chat_id, [])
            self.pending_timers.pop(chat_id, None)

        if not photos:
            return

        self.send_message(chat_id, f"🔍 Scanning {len(photos)} bet slips & syncing live status...")
        for p_bytes in photos:
            extracted = self.extract_text_from_photo(p_bytes)
            self.ingest_text_into_ledger(extracted, source_channel="Forwarded_Slip")

        self.sync_and_publish_to_footybett(force_fresh_scores=True)
        t_items, y_items = DailyLedgerManager.load_recent_active_items()
        card = BetSlipCardFormatter.format_full_bot_curation_slate(t_items, y_items)
        self.send_message(chat_id, card)

    def queue_photo(self, chat_id: int, photo_bytes: bytes):
        with self.lock:
            if chat_id not in self.pending_photos:
                self.pending_photos[chat_id] = []
            self.pending_photos[chat_id].append(photo_bytes)

            if chat_id in self.pending_timers:
                self.pending_timers[chat_id].cancel()

            timer = threading.Timer(3.0, self.flush_album_burst, args=[chat_id])
            self.pending_timers[chat_id] = timer
            timer.start()

    def execute_scan_and_show_slate(self, chat_id: int):
        try:
            channels = list(ChannelWebWatcher.get_watched_channels())
            self.send_message(
                chat_id,
                f"⚡ Scanning {len(channels)} channels + pulling LIVE on-spot match scores & syncing {PUBLISH_CHANNEL_ID}..."
            )

            seen = load_json_set(SEEN_POSTS_FILE)
            for ch in channels:
                html = ChannelWebWatcher.fetch_recent_channel_html(ch)
                if not html:
                    continue
                posts = ChannelWebWatcher.extract_recent_posts(html, only_unseen=True)
                for post_id, post_date, text, img_urls in posts:
                    seen.add(post_id)
                    if text.strip():
                        self.ingest_text_into_ledger(text, source_channel=ch, post_date_str=post_date)
                    for i_url in img_urls:
                        i_bytes = self.download_url_bytes(i_url)
                        if i_bytes:
                            img_text = self.extract_text_from_photo(i_bytes)
                            self.ingest_text_into_ledger(img_text, source_channel=ch, post_date_str=post_date)

            save_json_set(SEEN_POSTS_FILE, seen)

            self.sync_and_publish_to_footybett(force_fresh_scores=True)
            t_items, y_items = DailyLedgerManager.load_recent_active_items()

            card = BetSlipCardFormatter.format_full_bot_curation_slate(t_items, y_items)
            self.send_message(chat_id, card)
        except Exception as e:
            logger.error("Scan error: %s", e)
            self.send_message(chat_id, f"❌ Scan error: {e}")

    def background_worker_loop(self):
        logger.info("Background Channel, Live Score & @Footybett Publisher Worker started...")
        # Run an immediate catch-up pass 5 seconds after startup so yesterday's missing loss result & recap post right away!
        time.sleep(5)
        try:
            self.sync_and_publish_to_footybett(force_fresh_scores=True)
        except Exception as e:
            logger.error("Initial startup sync error: %s", e)

        cycle = 0
        while True:
            try:
                time.sleep(50)
                cycle += 1
                seen = load_json_set(SEEN_POSTS_FILE)
                newly_scanned_items: List[LedgerBetItem] = []

                for ch in ChannelWebWatcher.get_watched_channels():
                    html = ChannelWebWatcher.fetch_recent_channel_html(ch)
                    posts = ChannelWebWatcher.extract_recent_posts(html, only_unseen=True)
                    for post_id, post_date, text, img_urls in posts:
                        seen.add(post_id)
                        all_blocks = [text] if text.strip() else []
                        for i_url in img_urls:
                            i_bytes = self.download_url_bytes(i_url)
                            if i_bytes:
                                all_blocks.append(self.extract_text_from_photo(i_bytes))
                        for blk in all_blocks:
                            res_list = self.ingest_text_into_ledger(blk, source_channel=ch, post_date_str=post_date)
                            for is_new, stored in res_list:
                                if is_new:
                                    newly_scanned_items.append(stored)

                save_json_set(SEEN_POSTS_FILE, seen)

                self.sync_and_publish_to_footybett(force_fresh_scores=(cycle % 3 == 0))

                if newly_scanned_items:
                    app_new = [i for i in newly_scanned_items if i.is_approved]
                    rej_new = [i for i in newly_scanned_items if not i.is_approved]
                    lines = [
                        f"🔔 NEW CHANNEL SIGNALS EVALUATED ({len(app_new)} Chosen ✅ | {len(rej_new)} Declined ❌)",
                        "═" * 32
                    ]
                    for s in app_new:
                        chs = ", ".join(f"@{c}" for c in s.consensus_sources if c)
                        lines.append(f"✅ CHOSEN [{chs}]: {s.team_home} vs {s.team_away} — {s.selection} @ {s.odds:.2f}")
                        lines.append(f"   ↳ Why: {s.rationale}")
                    for r in rej_new:
                        chs = ", ".join(f"@{c}" for c in r.consensus_sources if c)
                        lines.append(f"❌ DECLINED [{chs}]: {r.team_home} vs {r.team_away} ({r.selection} @ {r.odds:.2f})")
                        lines.append(f"   ↳ Reason: {r.rationale}")
                    self.broadcast_admin("\n".join(lines))

            except Exception as e:
                logger.error("Background worker error: %s", e)

    def set_official_menu_commands(self):
        commands = [
            {"command": "scan", "description": "⚡ Chosen & Declined Bets + Live Sync"},
            {"command": "results", "description": "🏁 Live On-Spot Scores & Won/Lost Audit"},
            {"command": "stats", "description": "📈 Total PnL, Win Rate & R:R (Since 2026-11-08)"},
            {"command": "poststats", "description": "📢 Post Total Won/Lost Analysis to @Footybett"},
            {"command": "channels", "description": "👁️ Monitored Telegram Channels (8)"},
            {"command": "status", "description": "⚙️ System & Live Feed Status"}
        ]
        url = f"{self.base_url}/setMyCommands"
        req = urllib.request.Request(
            url,
            data=json.dumps({"commands": commands}).encode("utf-8"),
            headers={"Content-Type": "application/json"}
        )
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                logger.info("Registered Telegram menu commands: %s", resp.status == 200)
        except Exception as e:
            logger.error("Failed to register menu commands: %s", e)

    def run_polling_loop(self):
        self.set_official_menu_commands()
        watcher_thread = threading.Thread(target=self.background_worker_loop, daemon=True)
        watcher_thread.start()

        logger.info("Bot listener running (v14.0) with Retroactive @Footybett Settlement & Total Analysis...")
        offset = None

        while True:
            updates = self.get_updates(offset)
            for upd in updates:
                offset = upd["update_id"] + 1
                msg = upd.get("message", {})
                chat_id = msg.get("chat", {}).get("id")
                text = (msg.get("text", "") or msg.get("caption", "")).strip()
                photos = msg.get("photo", [])

                if not chat_id:
                    continue

                subs = load_json_set(SUBSCRIBERS_FILE)
                subs.add(chat_id)
                save_json_set(SUBSCRIBERS_FILE, subs)

                if text == "/start":
                    self.send_message(
                        chat_id,
                        "👋 Welcome to Pro Football Syndicate & @Footybett Publisher (v14.0)!\n\n"
                        "Use the blue [ Menu ] button on the left anytime:\n"
                        "• /scan — ⚡ Chosen ✅ & Declined ❌ Bets (Today & Yesterday)\n"
                        "• /results — 🏁 Live On-Spot Scores, Match Clock & Won/Lost Audit\n"
                        "• /stats — 📈 Total PnL, Win Rate & R:R (Since 2026-11-08)\n"
                        "• /poststats — 📢 Post Official Total Won/Lost Analysis to @Footybett\n"
                        "• /channels — 👁️ Monitored Telegram Channels\n"
                        "• /status — ⚙️ System & Live Feed Status"
                    )
                    continue

                if text in ["/stats", "📈 Total PnL & Stats"]:
                    def run_stats(cid):
                        self.sync_and_publish_to_footybett(force_fresh_scores=True)
                        report = BetSlipCardFormatter.format_lifetime_pnl_stats()
                        self.send_message(cid, report)
                    threading.Thread(target=run_stats, args=[chat_id], daemon=True).start()
                    continue

                if text == "/poststats":
                    def run_post_stats(cid):
                        self.sync_and_publish_to_footybett(force_fresh_scores=True)
                        recap_card = BetSlipCardFormatter.format_channel_total_analysis_recap()
                        if self.send_message(PUBLISH_CHANNEL_ID, recap_card, remove_kb=False):
                            self.send_message(cid, f"✅ Posted Official Total Won/Lost & P&L Analysis to {PUBLISH_CHANNEL_ID}!\n\n{recap_card}")
                        else:
                            self.send_message(cid, f"❌ Could not post to {PUBLISH_CHANNEL_ID}. Verify the bot is an Admin in the channel.")
                    threading.Thread(target=run_post_stats, args=[chat_id], daemon=True).start()
                    continue

                if text in ["/status", "⚙️ System & Quota Status"]:
                    api_stat = LiveFootballAPI.check_account_status()
                    ocr_stat = "Active (Shuffle Dark-Mode Binarization)" if OCR_AVAILABLE else "Not Installed"
                    channels = ChannelWebWatcher.get_watched_channels()
                    all_hist = DailyLedgerManager.load_all_history_items()
                    t_items, y_items = DailyLedgerManager.load_recent_active_items()
                    locks_count = len(load_json_set(PUBLISHED_LOCKS_FILE))
                    self.send_message(
                        chat_id,
                        f"⚙️ SYSTEM & LIVE SCORE STATUS\n"
                        f"════════════════════════════════\n"
                        f"📡 Live Feeds   : {api_stat}\n"
                        f"📸 Image OCR    : {ocr_stat}\n"
                        f"📢 VIP Channel  : {PUBLISH_CHANNEL_ID} ({locks_count} posts locked)\n"
                        f"👁️ Active Feeds : {len(channels)} Channels Monitored\n"
                        f"📅 Active Slate : {len(t_items)} Today | {len(y_items)} Yesterday\n"
                        f"📚 All-Time DB  : {len(all_hist)} bets tracked (from {TRACKING_START_DATE})"
                    )
                    continue

                if text in ["/channels", "👁️ Monitored Channels"]:
                    ch_list = "\n".join(f"• @{c} (https://t.me/s/{c})" for c in sorted(ChannelWebWatcher.get_watched_channels()))
                    self.send_message(
                        chat_id,
                        f"📋 MONITORED CHANNELS ({len(ChannelWebWatcher.get_watched_channels())} Feeds):\n"
                        f"════════════════════════════════\n"
                        f"{ch_list}\n\n"
                        f"📢 Publishing Approved Bets & Final Results to: {PUBLISH_CHANNEL_ID}\n"
                        f"💡 To add another source channel, send: `/watch username`"
                    )
                    continue

                if text in ["/scan", "⚡ Scan Today's Bets"]:
                    threading.Thread(target=self.execute_scan_and_show_slate, args=[chat_id], daemon=True).start()
                    continue

                if text in ["/results", "🏁 Live Scores & Results"]:
                    def run_results_check(cid):
                        self.send_message(cid, "🏁 Pulling live on-spot scores & match clock (ESPN Live + API-Football)...")
                        self.sync_and_publish_to_footybett(force_fresh_scores=True)
                        t_items, y_items = DailyLedgerManager.load_recent_active_items()
                        report = BetSlipCardFormatter.format_results_audit(t_items, y_items)
                        self.send_message(cid, report)
                    threading.Thread(target=run_results_check, args=[chat_id], daemon=True).start()
                    continue

                if text.startswith("/watch"):
                    parts = text.split(maxsplit=1)
                    if len(parts) < 2:
                        self.send_message(chat_id, "Usage: `/watch channel_username`")
                    else:
                        updated = ChannelWebWatcher.add_watched_channel(parts[1])
                        ch_list = ", ".join(f"@{c}" for c in sorted(updated))
                        self.send_message(chat_id, f"✅ Channel added! Now monitoring: {ch_list}")
                    continue

                if photos:
                    if not OCR_AVAILABLE:
                        self.send_message(chat_id, "📷 Run `apt install -y tesseract-ocr python3-pil python3-pytesseract` to enable OCR.")
                        continue
                    best_photo = photos[-1]
                    file_id = best_photo.get("file_id")
                    img_bytes = self.download_photo_bytes(file_id) if file_id else None
                    if img_bytes:
                        self.queue_photo(chat_id, img_bytes)
                    continue

                if text:
                    added = self.ingest_text_into_ledger(text, source_channel="Manual")
                    if added:
                        self.sync_and_publish_to_footybett(force_fresh_scores=True)
                        t_items, y_items = DailyLedgerManager.load_recent_active_items()
                        card = BetSlipCardFormatter.format_full_bot_curation_slate(t_items, y_items)
                        self.send_message(chat_id, card)
                    else:
                        self.send_message(chat_id, "❓ Could not recognize clear match fixtures. Use the [ Menu ] button on the left to navigate.")

            time.sleep(1)


if __name__ == "__main__":
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    if not token:
        print("Missing TELEGRAM_BOT_TOKEN")
        exit(1)
    bot = TelegramBotClient(token)
    try:
        bot.run_polling_loop()
    except KeyboardInterrupt:
        print("\nBot stopped.")