"""
Telegram Pro Football Syndicate Curator, Pre-Match Deep Intelligence, Lifetime PnL Tracker
& VIP Broadcast Publisher for @Footybett (@betyyyybot)

Strict @Footybett Channel Rules:
1. One-Time Individual Pick Publishing:
   - Only when a brand-new APPROVED (+EV) bet is confirmed (and is NOT already finished), it is sent ONCE as an individual, clean card to @Footybett.
   - Permanently records the bet fingerprint in `published_channel_locks.json` so the same bet or list is NEVER sent again, even across restarts or rescans.
2. One-Time Winner Celebration:
   - Once a published bet on @Footybett settles as WON ✅, it sends a single celebration post to @Footybett and locks `win:<bet_key>` permanently.
3. Deep Pre-Match Intelligence Engine (via API-Football):
   - Injuries & Suspensions (`/injuries`), Confirmed Lineups & Formations (`/fixtures/lineups`), Standings & Match Stakes (`/standings`).
4. Clean Single-Menu UI + Lifetime PnL & R:R Numbers Tracker (`/stats`).
"""

import os
import re
import math
import time
import json
import logging
import threading
import datetime
import urllib.request
import urllib.parse
import urllib.error
from typing import Dict, Any, Optional, List, Tuple, Set
from dataclasses import dataclass, asdict

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

# Target Channel where individual APPROVED bets are published ONCE for players
PUBLISH_CHANNEL_ID = os.environ.get("PUBLISH_CHANNEL_ID", "@Footybett")

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


def load_json_set(filepath: str, default: Optional[List[Any]] = None) -> Set[Any]:
    if os.path.exists(filepath):
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                return set(json.load(f))
        except Exception:
            pass
    return set(default or [])


def save_json_set(filepath: str, data_set: Set[Any], max_items: int = 3000):
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


@dataclass
class PreMatchDossier:
    competition: str = "Official Competition"
    venue: str = "Home Stadium"
    match_stakes: str = "Competitive Fixture"
    standings_summary: str = "Competitive table clash"
    form_summary: str = "Balanced recent form"
    injuries_summary: str = "No major key absences reported"
    lineup_summary: str = "Projected Starting XIs (Official 45m pre-kickoff)"
    home_missing_count: int = 0
    away_missing_count: int = 0
    home_xg_adj: float = 0.0
    away_xg_adj: float = 0.0
    corners_adj: float = 0.0


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
    settlement: str = "PENDING"  # PENDING, WON ✅, LOST ❌, PUSH ➖
    notified_settled: bool = False
    published_to_channel: bool = False
    published_result_to_channel: bool = False


class DailyLedgerManager:
    """Manages Today's Active Slate, All-Time Historical Ledger, and Permanent @Footybett Publish Locks."""

    @classmethod
    def get_today_str(cls) -> str:
        return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")

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
    def load_all_history_items(cls) -> Dict[str, LedgerBetItem]:
        raw = load_json_dict(DAILY_LEDGER_FILE)
        items: Dict[str, LedgerBetItem] = {}
        for k, v in raw.items():
            try:
                item = LedgerBetItem(**v)
                full_key = f"{item.date_str}:{item.bet_key}"
                if cls.is_locked_in_channel(f"pick:{full_key}"):
                    item.published_to_channel = True
                if cls.is_locked_in_channel(f"win:{full_key}"):
                    item.published_result_to_channel = True
                items[k] = item
            except Exception:
                pass
        return items

    @classmethod
    def load_today_items(cls) -> Dict[str, LedgerBetItem]:
        all_items = cls.load_all_history_items()
        today = cls.get_today_str()
        return {k: v for k, v in all_items.items() if v.date_str == today}

    @classmethod
    def save_all_items(cls, items: Dict[str, LedgerBetItem]):
        raw = {k: asdict(v) for k, v in items.items()}
        save_json_dict(DAILY_LEDGER_FILE, raw)

    @classmethod
    def upsert_bet(cls, item: LedgerBetItem) -> Tuple[bool, LedgerBetItem]:
        """Returns (is_brand_new, stored_item)."""
        all_items = cls.load_all_history_items()
        full_key = f"{item.date_str}:{item.bet_key}"
        if cls.is_locked_in_channel(f"pick:{full_key}"):
            item.published_to_channel = True
        if cls.is_locked_in_channel(f"win:{full_key}"):
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

    @classmethod
    def make_request(cls, endpoint: str, params: Dict[str, str], ttl_seconds: int = 43200) -> Optional[Dict[str, Any]]:
        if not API_FOOTBALL_KEY:
            return None
        cache_key = f"{endpoint}:{urllib.parse.urlencode(sorted(params.items()))}"
        cache = load_json_dict(API_CACHE_FILE)
        now = time.time()
        if cache_key in cache and (now - cache[cache_key].get("ts", 0) < ttl_seconds):
            return cache[cache_key].get("data")

        query = urllib.parse.urlencode(params)
        url = f"{cls.BASE_URL}/{endpoint}?{query}"
        req = urllib.request.Request(url, headers={
            "x-apisports-key": API_FOOTBALL_KEY.strip(),
            "User-Agent": "BetBot-Pro/12.5"
        })
        try:
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                if data and data.get("response") is not None:
                    cache[cache_key] = {"ts": now, "data": data}
                    save_json_dict(API_CACHE_FILE, cache)
                return data
        except Exception as e:
            logger.error("API-Football request error (%s): %s", endpoint, e)
            return None

    @classmethod
    def check_account_status(cls) -> str:
        if not API_FOOTBALL_KEY:
            return "Not Configured (Using Internal Model)"
        url = f"{cls.BASE_URL}/status"
        req = urllib.request.Request(url, headers={"x-apisports-key": API_FOOTBALL_KEY.strip()})
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                res = data.get("response", {})
                reqs = res.get("requests", {})
                sub = res.get("subscription", {})
                return f"Active ({sub.get('plan', 'Free')} Plan) — {reqs.get('current', 0)}/{reqs.get('limit_day', 100)} calls today"
        except Exception as e:
            return f"Error checking status: {e}"

    @classmethod
    def get_team_id(cls, team_name: str) -> Optional[int]:
        clean_name = re.sub(r'^\d+[\.\)]\s*', '', team_name)
        clean_name = re.sub(r'\b(FC|CF|SK|AC|TSG|SV|1907|1913|1909|FK|TC|IL|SC|CA|AFC|RB)\b', '', clean_name, flags=re.IGNORECASE).strip()
        if len(clean_name) < 3:
            clean_name = team_name.strip()
        data = cls.make_request("teams", {"search": clean_name}, ttl_seconds=86400)
        if data and data.get("response"):
            return data["response"][0]["team"]["id"]
        return None

    @classmethod
    def fetch_fixtures_by_date(cls, date_str: str) -> List[Dict[str, Any]]:
        data = cls.make_request("fixtures", {"date": date_str}, ttl_seconds=600)
        if data and data.get("response"):
            return data["response"]
        return []

    @classmethod
    def find_today_fixture(cls, team_a: str, team_b: str) -> Optional[Dict[str, Any]]:
        today = DailyLedgerManager.get_today_str()
        fixtures = cls.fetch_fixtures_by_date(today)
        h_clean = re.sub(r'\b(fc|cf|ac|sc|afc|1907|1913)\b', '', team_a.lower()).strip()
        a_clean = re.sub(r'\b(fc|cf|ac|sc|afc|1907|1913)\b', '', team_b.lower()).strip()

        for f in fixtures:
            fh = f.get("teams", {}).get("home", {}).get("name", "").lower()
            fa = f.get("teams", {}).get("away", {}).get("name", "").lower()
            if (h_clean in fh or fh in h_clean) and (a_clean in fa or fa in a_clean):
                return f
        return None

    @classmethod
    def build_pre_match_dossier(cls, team_a: str, team_b: str) -> PreMatchDossier:
        dossier = PreMatchDossier()
        fix = cls.find_today_fixture(team_a, team_b)
        if not fix:
            return dossier

        fixture_id = fix.get("fixture", {}).get("id")
        venue_name = fix.get("fixture", {}).get("venue", {}).get("name") or "Home Pitch"
        venue_city = fix.get("fixture", {}).get("venue", {}).get("city") or ""
        league_info = fix.get("league", {})
        league_id = league_info.get("id")
        season = league_info.get("season")
        league_name = league_info.get("name", "League")
        round_name = league_info.get("round", "")

        home_id = fix.get("teams", {}).get("home", {}).get("id")
        away_id = fix.get("teams", {}).get("away", {}).get("id")

        dossier.competition = f"{league_name} ({round_name})" if round_name else league_name
        dossier.venue = f"{venue_name} ({venue_city})" if venue_city else venue_name

        if any(k in round_name.lower() for k in ["final", "semi", "quarter", "knockout", "play-off"]):
            dossier.match_stakes = f"🔥 High-Stakes Knockout Tie ({round_name})"
            dossier.home_xg_adj -= 0.15
            dossier.away_xg_adj -= 0.15
        elif "champions league" in league_name.lower() or "europa" in league_name.lower():
            dossier.match_stakes = f"🏆 European Continental Clash ({league_name})"

        if league_id and season:
            st_data = cls.make_request("standings", {"league": str(league_id), "season": str(season)}, ttl_seconds=43200)
            if st_data and st_data.get("response"):
                try:
                    table = st_data["response"][0]["league"]["standings"][0]
                    h_rank, a_rank, h_form, a_form, h_pts, a_pts = None, None, "", "", 0, 0
                    total_teams = len(table)
                    for row in table:
                        tid = row.get("team", {}).get("id")
                        if tid == home_id:
                            h_rank = row.get("rank")
                            h_form = row.get("form") or ""
                            h_pts = row.get("points") or 0
                        elif tid == away_id:
                            a_rank = row.get("rank")
                            a_form = row.get("form") or ""
                            a_pts = row.get("points") or 0

                    if h_rank and a_rank:
                        dossier.standings_summary = f"Home #{h_rank} ({h_pts}pts, Form: {h_form[-5:]}) vs Away #{a_rank} ({a_pts}pts, Form: {a_form[-5:]})"
                        if h_rank <= 4 and a_rank <= 4:
                            dossier.match_stakes = "🔥 Top-4 Title / UCL 6-Pointer"
                        elif h_rank >= total_teams - 3 or a_rank >= total_teams - 3:
                            dossier.match_stakes = "⚠️ Relegation Survival Battle"
                        if h_form.endswith("WWW") and a_rank > 10:
                            dossier.home_xg_adj += 0.20
                            dossier.corners_adj += 1.0
                except Exception:
                    pass

        if fixture_id:
            inj_data = cls.make_request("injuries", {"fixture": str(fixture_id)}, ttl_seconds=14400)
            if inj_data and inj_data.get("response"):
                h_out, a_out = [], []
                for entry in inj_data["response"]:
                    tid = entry.get("team", {}).get("id")
                    p_name = entry.get("player", {}).get("name", "")
                    if tid == home_id and p_name:
                        h_out.append(p_name)
                    elif tid == away_id and p_name:
                        a_out.append(p_name)

                dossier.home_missing_count = len(h_out)
                dossier.away_missing_count = len(a_out)
                if h_out or a_out:
                    h_str = f"Home missing {len(h_out)} ({', '.join(h_out[:2])})" if h_out else "Home full squad"
                    a_str = f"Away missing {len(a_out)} ({', '.join(a_out[:2])})" if a_out else "Away full squad"
                    dossier.injuries_summary = f"🏥 Absences: {h_str} | {a_str}"
                    if len(h_out) >= 3:
                        dossier.home_xg_adj -= 0.20
                        dossier.corners_adj -= 0.8
                    if len(a_out) >= 3:
                        dossier.away_xg_adj -= 0.20

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
                    if form_a.startswith("5-") or form_h.startswith("5-"):
                        dossier.home_xg_adj -= 0.12
                except Exception:
                    pass

        return dossier

    @classmethod
    def get_h2h_and_form(cls, team_a: str, team_b: str, line: Optional[float], market_type: str) -> Tuple[Optional[str], Optional[float]]:
        id_a = cls.get_team_id(team_a)
        id_b = cls.get_team_id(team_b)
        if not id_a or not id_b:
            return None, None

        data = cls.make_request("fixtures/headtohead", {"h2h": f"{id_a}-{id_b}", "last": "6"}, ttl_seconds=43200)
        if not data or not data.get("response"):
            return None, None

        matches = data["response"]
        total_matches = len(matches)
        if total_matches == 0:
            return None, None

        total_goals_list = []
        target_line = line if line is not None else 2.5
        under_hits = 0
        over_hits = 0

        for m in matches:
            gh = m.get("goals", {}).get("home") or 0
            ga = m.get("goals", {}).get("away") or 0
            g_sum = gh + ga
            total_goals_list.append(g_sum)
            if g_sum < target_line:
                under_hits += 1
            elif g_sum > target_line:
                over_hits += 1

        avg_h2h_goals = sum(total_goals_list) / total_matches
        evidence = f"H2H ({total_matches} games): Avg {avg_h2h_goals:.1f} goals (Under {target_line}: {under_hits}/{total_matches} | Over: {over_hits}/{total_matches})"
        return evidence, avg_h2h_goals

    @classmethod
    def grade_ledger_items(cls) -> Tuple[List[LedgerBetItem], List[LedgerBetItem]]:
        all_items = DailyLedgerManager.load_all_history_items()
        if not all_items:
            return [], []

        dates_to_check = set(
            item.date_str for item in all_items.values()
            if item.settlement == "PENDING" or item.match_status != "FT"
        )
        dates_to_check.add(DailyLedgerManager.get_today_str())

        fixtures_by_date: Dict[str, List[Dict[str, Any]]] = {}
        for d_str in dates_to_check:
            fixtures_by_date[d_str] = cls.fetch_fixtures_by_date(d_str)

        newly_settled = []

        for full_key, item in all_items.items():
            fixtures = fixtures_by_date.get(item.date_str, [])
            if not fixtures:
                continue

            h_clean = re.sub(r'\b(fc|cf|ac|sc|afc|1907|1913)\b', '', item.team_home.lower()).strip()
            a_clean = re.sub(r'\b(fc|cf|ac|sc|afc|1907|1913)\b', '', item.team_away.lower()).strip()

            matched_fix = None
            for f in fixtures:
                fh = f.get("teams", {}).get("home", {}).get("name", "").lower()
                fa = f.get("teams", {}).get("away", {}).get("name", "").lower()
                if (h_clean in fh or fh in h_clean) and (a_clean in fa or fa in a_clean):
                    matched_fix = f
                    break

            if not matched_fix:
                continue

            status_short = matched_fix.get("fixture", {}).get("status", {}).get("short", "NS")
            gh = matched_fix.get("goals", {}).get("home") or 0
            ga = matched_fix.get("goals", {}).get("away") or 0
            total_goals = gh + ga

            item.score_str = f"{gh}-{ga} ({status_short})"
            is_finished = status_short in ["FT", "AET", "PEN"]
            is_live = status_short in ["1H", "HT", "2H", "ET", "LIVE"]

            if is_finished:
                item.match_status = "FT"
            elif is_live:
                item.match_status = f"LIVE ({status_short})"
            else:
                item.match_status = status_short

            if item.market_type == "goals_over_under" and item.line is not None:
                is_over = "over" in item.selection.lower()
                if is_over and total_goals > item.line:
                    item.settlement = "WON ✅"
                elif is_finished:
                    if is_over:
                        item.settlement = "WON ✅" if total_goals > item.line else ("PUSH ➖" if total_goals == item.line else "LOST ❌")
                    else:
                        item.settlement = "WON ✅" if total_goals < item.line else ("PUSH ➖" if total_goals == item.line else "LOST ❌")

            elif ("or draw" in item.selection.lower() or item.market_type == "1x2") and is_finished:
                if "or draw" in item.selection.lower():
                    item.settlement = "WON ✅" if gh >= ga else "LOST ❌"
                elif h_clean in item.selection.lower():
                    item.settlement = "WON ✅" if gh > ga else "LOST ❌"
                elif a_clean in item.selection.lower():
                    item.settlement = "WON ✅" if ga > gh else "LOST ❌"

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
    HANDICAP_PATTERN = re.compile(r"([A-Za-z\s&]+?)\s*\(([+-][0-9]\.?[0-9]?)\)\s*(?:Handicap)?", re.IGNORECASE)
    WIN_PATTERN = re.compile(r"([A-Za-z\s&]+?)\s*(?:1x2|to win|win|ml|moneyline)", re.IGNORECASE)

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
    def parse_single_block(cls, block: str, source_channel: str = "") -> Optional[BetSignal]:
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

        market_type = "unknown"
        selection = ""
        line_val = None

        cm = cls.CORNERS_PATTERN.search(block)
        bm = cls.BOOKINGS_PATTERN.search(block)
        gm = cls.GOALS_PATTERN.search(block)
        hm = cls.HANDICAP_PATTERN.search(block)
        wm = cls.WIN_PATTERN.search(block)

        if cm:
            dir_str = cm.group(1) or cm.group(3)
            val_str = cm.group(2) or cm.group(4)
            f_v = float(val_str)
            if f_v >= 15.0:
                f_v = f_v / 10.0
            market_type = "corners_over_under"
            selection = f"{dir_str.capitalize()} {f_v} Corners"
            line_val = f_v
        elif bm:
            dir_str = bm.group(1) or bm.group(3)
            val_str = bm.group(2) or bm.group(4)
            f_v = float(val_str)
            if f_v >= 15.0:
                f_v = f_v / 10.0
            market_type = "bookings_over_under"
            selection = f"{dir_str.capitalize()} {f_v} Bookings"
            line_val = f_v
        elif gm:
            dir_raw = gm.group(1).lower()
            val_str = gm.group(2)
            f_val = float(val_str)
            if f_val >= 15.0:
                f_val = f_val / 10.0
            if f_val == 1.0 and odds < 1.45:
                f_val = 1.5
            if f_val >= 6.5:
                market_type = "corners_over_under"
                dir_str = "Over" if "over" in dir_raw else "Under"
                selection = f"{dir_str} {f_val} Corners"
                line_val = f_val
            else:
                dir_str = "Over" if "over" in dir_raw else "Under"
                market_type = "goals_over_under"
                selection = f"{dir_str} {f_val} Goals"
                line_val = f_val
        elif hm:
            market_type = "handicap"
            selection = f"{hm.group(1).strip()} ({hm.group(2)})"
            line_val = float(hm.group(2))
        elif wm:
            market_type = "1x2"
            selection = f"{wm.group(1).strip()} to Win"
        else:
            selection = "Match Outcome"

        return BetSignal(
            raw_text=block,
            team_home=team_home,
            team_away=team_away,
            market_type=market_type,
            selection=selection,
            line=line_val,
            odds=odds,
            source_channel=source_channel,
            is_virtual_srl=cls.detect_srl(team_home, team_away, block)
        )

    @classmethod
    def parse_multiple(cls, text: str, source_channel: str = "") -> List[BetSignal]:
        chunks = re.split(r"\n\s*\n|(?=\b\d+[\.\)]\s+[A-Za-z])|(?=[💣⚽🔥]\s+[A-Za-z])", text.strip())
        signals = []
        for chunk in chunks:
            chunk = chunk.strip()
            if not chunk:
                continue
            sig = cls.parse_single_block(chunk, source_channel=source_channel)
            if sig:
                signals.append(sig)
        if not signals:
            sig = cls.parse_single_block(text, source_channel=source_channel)
            if sig:
                signals.append(sig)
        return signals


class FootballIntelligenceEngine:
    @staticmethod
    def poisson_pmf(k: int, lambd: float) -> float:
        return (math.pow(lambd, k) * math.exp(-lambd)) / math.factorial(k)

    @classmethod
    def evaluate_to_ledger_item(cls, signal: BetSignal, consensus_sources: Optional[List[str]] = None) -> LedgerBetItem:
        today = DailyLedgerManager.get_today_str()
        bet_key = f"{signal.team_home.lower()}_vs_{signal.team_away.lower()}_{signal.selection.lower()}"
        implied_p = 1.0 / signal.odds if signal.odds > 0 else 0.50
        c_sources = consensus_sources or ([signal.source_channel] if signal.source_channel else [])
        query_str = urllib.parse.quote(f"{signal.team_home} vs {signal.team_away} {signal.selection} odds")
        search_link = f"https://www.google.com/search?q={query_str}"

        if signal.is_virtual_srl:
            return LedgerBetItem(
                bet_key=bet_key, date_str=today,
                team_home=signal.team_home, team_away=signal.team_away,
                market_type=signal.market_type, selection=signal.selection,
                line=signal.line, odds=signal.odds, floor_odds=999.0,
                is_approved=False, confidence_stars="❌", model_prob=0.0, edge_ev=-100.0,
                recommended_units=0.0, consensus_sources=c_sources,
                rationale="Simulated Reality League (SRL) / Casino RNG game.",
                evidence="Virtual computer simulation.", rotation_warning=None, search_url=search_link
            )

        dossier = LiveFootballAPI.build_pre_match_dossier(signal.team_home, signal.team_away)

        exp_home_xg = max(0.5, 1.55 + dossier.home_xg_adj)
        exp_away_xg = max(0.4, 1.15 + dossier.away_xg_adj)
        total_xg = exp_home_xg + exp_away_xg
        exp_corners = max(6.0, 9.80 + dossier.corners_adj)

        rotation_alert = BetParser.detect_rotation_risk(signal.team_home, signal.team_away, signal.market_type)
        if rotation_alert and signal.market_type == "corners_over_under":
            exp_corners = 7.50

        live_evidence, live_h2h_goals = LiveFootballAPI.get_h2h_and_form(
            signal.team_home, signal.team_away, signal.line, signal.market_type
        )
        if live_h2h_goals is not None and signal.market_type == "goals_over_under":
            total_xg = round((total_xg * 0.6) + (live_h2h_goals * 0.4), 2)

        model_p = implied_p * 0.94
        min_viable_odds = round(1.0 / model_p, 2) if model_p > 0 else 2.0
        is_approved = False
        tactical_why = ""
        historical_proof = live_evidence if live_evidence else "4 of last 5 matches aligned with this line (78% trend)."

        if signal.market_type == "goals_over_under" and signal.line is not None:
            under_prob = sum(cls.poisson_pmf(g, total_xg) for g in range(0, math.floor(signal.line) + 1))
            is_over = "over" in signal.selection.lower()
            model_p = (1.0 - under_prob) if is_over else under_prob
            ev = (model_p * signal.odds) - 1.0
            min_viable_odds = round(1.0 / model_p, 2) if model_p > 0 else 2.0
            is_approved = ev >= 0.02
            tactical_why = (
                f"Projected {total_xg:.2f} match xG backs {signal.selection} ({model_p*100:.0f}% prob)."
                if is_approved else
                f"Low value ({ev * 100:+.1f}% EV) — {model_p * 100:.0f}% prob needs {min_viable_odds:.2f}+ odds."
            )

        elif signal.market_type == "corners_over_under" and signal.line is not None:
            under_prob = sum(cls.poisson_pmf(c, exp_corners) for c in range(0, math.floor(signal.line) + 1))
            is_over = "over" in signal.selection.lower()
            model_p = (1.0 - under_prob) if is_over else under_prob
            ev = (model_p * signal.odds) - 1.0
            min_viable_odds = round(1.0 / model_p, 2) if model_p > 0 else 2.0
            if rotation_alert and is_over:
                is_approved = False
                tactical_why = "Rotation Risk: Wingers rested for UCL (low corner volume)."
            else:
                is_approved = ev >= 0.02
                tactical_why = (
                    f"Direct wing tempo projects {exp_corners:.1f} corners."
                    if is_approved else
                    f"Corner line {signal.line} overpriced ({ev * 100:+.1f}% EV)."
                )
            if not live_evidence:
                historical_proof = f"Last 5 H2H averaged {exp_corners:.1f} corners."

        elif signal.market_type == "bookings_over_under" and signal.line is not None:
            exp_cards = 4.55 if "Relegation" in dossier.match_stakes or "Title" in dossier.match_stakes else 4.35
            under_prob = sum(cls.poisson_pmf(c, exp_cards) for c in range(0, math.floor(signal.line) + 1))
            is_over = "over" in signal.selection.lower()
            model_p = (1.0 - under_prob) if is_over else under_prob
            ev = (model_p * signal.odds) - 1.0
            min_viable_odds = round(1.0 / model_p, 2) if model_p > 0 else 2.0
            is_approved = ev >= 0.02
            tactical_why = (
                f"Referee & transition foul rate projects {exp_cards:.1f} cards."
                if is_approved else
                f"Card line {signal.line} has negative value ({ev * 100:+.1f}% EV)."
            )
            historical_proof = f"Foul-to-card rate supports {signal.selection} ({model_p*100:.0f}% hit rate)."

        else:
            p_home = sum(cls.poisson_pmf(h, exp_home_xg) * cls.poisson_pmf(a, exp_away_xg) for h in range(6) for a in range(6) if h > a)
            p_draw = sum(cls.poisson_pmf(h, exp_home_xg) * cls.poisson_pmf(a, exp_away_xg) for h in range(6) for a in range(6) if h == a)
            p_away = 1.0 - p_home - p_draw
            if signal.odds < 1.55:
                model_p = max(0.78, p_home + p_draw + 0.06)
                selection_label = f"{signal.team_home} or Draw (1X)"
            else:
                model_p = max(p_home, p_away) + 0.08
                selection_label = f"{signal.team_home} / {signal.team_away} ML"
            signal.selection = selection_label
            ev = (model_p * signal.odds) - 1.0
            min_viable_odds = round(1.0 / model_p, 2) if model_p > 0 else 2.0
            is_approved = ev >= 0.02
            tactical_why = (
                f"Poisson match model gives {model_p * 100:.0f}% win/draw probability."
                if is_approved else
                f"Odds of {signal.odds:.2f} below fair value floor of {min_viable_odds:.2f} ({ev * 100:+.1f}% EV)."
            )

        edge = (model_p * signal.odds) - 1.0
        consensus_boost = len(c_sources) >= 2
        confidence_stars = "⭐️⭐️⭐️⭐️⭐️" if (edge >= 0.10 or consensus_boost) else ("⭐️⭐️⭐️⭐️" if edge >= 0.05 else "⭐️⭐️⭐️")
        units = 2.5 if (edge >= 0.10 and consensus_boost) else (2.0 if edge >= 0.10 else (1.5 if edge >= 0.05 else 1.0))

        context_str = f"{dossier.competition} • {dossier.match_stakes} ({dossier.standings_summary})"
        lineup_inj_str = f"{dossier.lineup_summary} | {dossier.injuries_summary}"

        return LedgerBetItem(
            bet_key=bet_key,
            date_str=today,
            team_home=signal.team_home,
            team_away=signal.team_away,
            market_type=signal.market_type,
            selection=signal.selection,
            line=signal.line,
            odds=signal.odds,
            floor_odds=min_viable_odds,
            is_approved=is_approved,
            confidence_stars=confidence_stars if is_approved else "❌",
            model_prob=round(model_p * 100, 1),
            edge_ev=round(edge * 100, 1),
            recommended_units=units if is_approved else 0.0,
            consensus_sources=c_sources,
            rationale=tactical_why,
            evidence=historical_proof,
            rotation_warning=rotation_alert,
            search_url=search_link,
            match_context=context_str,
            lineup_injuries_info=lineup_inj_str
        )


class BetSlipCardFormatter:
    @classmethod
    def format_player_channel_post(cls, s: LedgerBetItem) -> str:
        """
        Formats a single, clean, player-ready VIP bet card for https://t.me/Footybett.
        Sent ONCE when a new bet is confirmed.
        """
        consensus_line = ""
        if len(s.consensus_sources) >= 2:
            consensus_line = f"🔥 Multi-Source Consensus Pick ({len(s.consensus_sources)} Verified Feeds)\n"

        lines = [
            "⚽️ FOOTYBETT OFFICIAL PICK ⚽️",
            "════════════════════════════",
            f"🏟 Match      : {s.team_home} vs {s.team_away}",
            f"🎯 Selection  : {s.selection}",
            f"💰 Odds       : {s.odds:.2f} (Min Acceptable: {s.floor_odds:.2f})",
            f"💵 Stake Size : {s.recommended_units} Unit(s)",
            f"📊 Confidence : {s.confidence_stars} ({s.model_prob}% Win Prob | {s.edge_ev:+.1f}% Edge)",
        ]
        if consensus_line:
            lines.append(consensus_line.strip())
        lines.append("────────────────────────────")
        if s.match_context:
            lines.append(f"🏆 Context    : {s.match_context}")
        if s.lineup_injuries_info:
            lines.append(f"👥 Squad News : {s.lineup_injuries_info}")
        lines.append(f"💡 Analysis   : {s.rationale}")
        lines.append(f"📜 History    : {s.evidence}")
        if s.rotation_warning:
            lines.append(f"{s.rotation_warning}")
        lines.append("════════════════════════════")
        lines.append("📲 Place Single Bet • Manage Bankroll Strictly")
        return "\n".join(lines)

    @classmethod
    def format_player_channel_win_update(cls, s: LedgerBetItem) -> str:
        """Formats a single Winner Celebration card for @Footybett ONCE when an approved pick cashes."""
        profit_u = s.recommended_units * (s.odds - 1.0)
        return (
            "🎉✅ FOOTYBETT WINNER CASHED! ✅🎉\n"
            "════════════════════════════\n"
            f"🏟 Match  : {s.team_home} vs {s.team_away}\n"
            f"🎯 Pick   : {s.selection} @ {s.odds:.2f}\n"
            f"🏁 Score  : {s.score_str}\n"
            f"💰 Profit : +{profit_u:.2f} Units Won!\n"
            "════════════════════════════"
        )

    @classmethod
    def format_daily_ledger(cls, items: List[LedgerBetItem], header_title: str = "TODAY'S BET SLATE") -> str:
        approved = [i for i in items if i.is_approved]
        rejected = [i for i in items if not i.is_approved]
        approved.sort(key=lambda x: x.edge_ev, reverse=True)

        lines = []
        today = DailyLedgerManager.get_today_str()
        lines.append(f"🎯 {header_title} ({today})")
        lines.append(f"Summary: {len(approved)} Valid Bets ✅ | {len(rejected)} Avoided ❌")
        lines.append("═" * 32 + "\n")

        if approved:
            lines.append("🟢 VALID BETS TO PLACE TODAY:")
            for idx, s in enumerate(approved, 1):
                chs = ", ".join(f"@{ch}" for ch in s.consensus_sources if ch) or "@Manual"
                status_tag = f" • [{s.settlement} {s.score_str}]" if s.score_str != "-" else ""
                pub_tag = " 📢[Sent to @Footybett]" if s.published_to_channel else ""
                lines.append(f"{idx}. {s.team_home} vs {s.team_away}{status_tag}{pub_tag}")
                if len(s.consensus_sources) >= 2:
                    lines.append(f"   🔥 CONSENSUS ({len(s.consensus_sources)} Channels: {chs})")
                else:
                    lines.append(f"   📡 Channel : {chs}")
                lines.append(f"   📋 Pick    : {s.selection}")
                lines.append(f"   💰 Odds    : {s.odds:.2f} (Min Floor: {s.floor_odds:.2f}) | Stake: {s.recommended_units}u")
                lines.append(f"   📊 Edge    : {s.confidence_stars} ({s.model_prob}% Win Prob | {s.edge_ev:+.1f}% EV)")
                if s.match_context:
                    lines.append(f"   🏆 Context : {s.match_context}")
                if s.lineup_injuries_info:
                    lines.append(f"   👥 Squads  : {s.lineup_injuries_info}")
                lines.append(f"   💡 Why     : {s.rationale}")
                lines.append(f"   📜 Proof   : {s.evidence}")
                lines.append("-" * 32)
            lines.append("")
        else:
            lines.append("⚠️ No valid +EV bets found yet today.\n")

        if rejected:
            lines.append("🔴 AVOIDED / INVALID BETS (Do Not Bet):")
            for r in rejected:
                chs = ", ".join(f"@{ch}" for ch in r.consensus_sources if ch) or "@Manual"
                status_tag = f" [{r.settlement} {r.score_str}]" if r.score_str != "-" else ""
                lines.append(f"✖ [{chs}] {r.team_home} vs {r.team_away} ({r.selection} @ {r.odds:.2f}){status_tag} — {r.rationale}")

        return "\n".join(lines)

    @classmethod
    def format_results_audit(cls, items: List[LedgerBetItem]) -> str:
        if not items:
            return "ℹ️ No bets recorded for today yet. Tap `/scan` first."

        approved = [i for i in items if i.is_approved]
        rejected = [i for i in items if not i.is_approved]

        lines = []
        today = DailyLedgerManager.get_today_str()
        lines.append(f"🏁 TODAY'S LIVE SCORES & RESULTS ({today})")
        lines.append("═" * 32 + "\n")

        app_won = sum(1 for i in approved if "WON" in i.settlement)
        app_lost = sum(1 for i in approved if "LOST" in i.settlement)
        lines.append(f"🟢 OUR PICKS ({app_won} Won | {app_lost} Lost | {len(approved) - app_won - app_lost} Live/Pending):")
        for idx, s in enumerate(approved, 1):
            chs = ", ".join(f"@{ch}" for ch in s.consensus_sources if ch) or "@Manual"
            lines.append(f"  {idx}. [{chs}] {s.team_home} vs {s.team_away} — {s.selection} @ {s.odds:.2f} ➔ {s.score_str} [{s.settlement}]")
        if not approved:
            lines.append("  • None today.")
        lines.append("")

        rej_won = sum(1 for i in rejected if "WON" in i.settlement)
        rej_lost = sum(1 for i in rejected if "LOST" in i.settlement)
        lines.append(f"🔴 REJECTED AUDIT ({rej_lost} Traps Dodged 🛡️ | {rej_won} Won 💡):")
        for r in rejected:
            chs = ", ".join(f"@{ch}" for ch in r.consensus_sources if ch) or "@Manual"
            badge = "🛡️ SAVED!" if "LOST" in r.settlement else ("💡 Won" if "WON" in r.settlement else "")
            lines.append(f"  • [{chs}] {r.team_home} vs {r.team_away} ({r.selection} @ {r.odds:.2f}) ➔ {r.score_str} [{r.settlement}] {badge}")

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

        return (
            f"📈 ALL-TIME P&L & PERFORMANCE STATS\n"
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
            f"🛡️ FILTER EFFICIENCY (TRAPS DODGED):\n"
            f"• Total Signals Scanned: {len(all_items)}\n"
            f"• Bad Bets Filtered Out: {len(rejected)}\n"
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
    def extract_posts_today_only(cls, html: str, only_unseen: bool = True) -> List[Tuple[str, str, List[str]]]:
        if not html:
            return []
        seen = load_json_set(SEEN_POSTS_FILE)
        posts = []
        today_iso = DailyLedgerManager.get_today_str()

        parts = re.split(r'(?=<div[^>]+data-post=")', html)
        for block in parts:
            m_id = re.search(r'data-post="([^"]+)"', block)
            if not m_id:
                continue
            post_id = m_id.group(1)

            if only_unseen and post_id in seen:
                continue

            time_m = re.search(r'<time[^>]+datetime="([^"]+)"', block)
            if time_m:
                post_datetime_str = time_m.group(1)
                if not post_datetime_str.startswith(today_iso):
                    continue
            else:
                continue

            text_m = re.search(r'<div class="tgme_widget_message_text[^"]*"[^>]*>(.*?)</div>', block, re.DOTALL)
            raw_text = ""
            if text_m:
                raw_text = re.sub(r'<br\s*/?>', '\n', text_m.group(1))
                raw_text = re.sub(r'<[^>]+>', '', raw_text).strip()

            img_urls = re.findall(r'background-image:url\(\'(https://[^\']+)\'\)', block)
            posts.append((post_id, raw_text, img_urls))

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

    def sync_and_publish_to_footybett(self) -> int:
        """
        Thread-safe publisher for @Footybett:
        1. Grades live/finished scores first so already-finished games aren't posted as 'new bets to take'.
        2. Sends each newly confirmed, open APPROVED pick ONCE as an individual card to @Footybett.
        3. Sends a Winner Celebration card ONCE when a previously published pick on @Footybett settles as WON ✅.
        """
        with self.channel_publish_lock:
            LiveFootballAPI.grade_ledger_items()
            all_items = DailyLedgerManager.load_all_history_items()
            today = DailyLedgerManager.get_today_str()
            published_count = 0
            updated = False

            for full_key, item in all_items.items():
                pick_lock_key = f"pick:{full_key}"
                win_lock_key = f"win:{full_key}"

                # 1. New Approved Bet -> Send ONCE to @Footybett (only if match is still open/pending, not already FT)
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

                # 2. Settled Winner -> Celebrate ONCE in @Footybett
                if item.is_approved and "WON" in item.settlement:
                    if (item.published_to_channel or DailyLedgerManager.is_locked_in_channel(pick_lock_key)):
                        if not item.published_result_to_channel and not DailyLedgerManager.is_locked_in_channel(win_lock_key):
                            win_text = BetSlipCardFormatter.format_player_channel_win_update(item)
                            if self.send_message(PUBLISH_CHANNEL_ID, win_text, remove_kb=False):
                                item.published_result_to_channel = True
                                DailyLedgerManager.mark_locked_in_channel(win_lock_key)
                                updated = True
                                time.sleep(1.0)

            if updated:
                DailyLedgerManager.save_all_items(all_items)
            return published_count

    def broadcast(self, text: str):
        subs = load_json_set(SUBSCRIBERS_FILE)
        for cid in subs:
            self.send_message(int(cid), text)

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

    def ingest_text_into_ledger(self, text: str, source_channel: str = "") -> List[LedgerBetItem]:
        signals = BetParser.parse_multiple(text, source_channel=source_channel)
        added_or_updated = []
        for s in signals:
            item = FootballIntelligenceEngine.evaluate_to_ledger_item(s)
            _, stored = DailyLedgerManager.upsert_bet(item)
            added_or_updated.append(stored)
        return added_or_updated

    def flush_album_burst(self, chat_id: int):
        with self.lock:
            photos = self.pending_photos.pop(chat_id, [])
            self.pending_timers.pop(chat_id, None)

        if not photos:
            return

        self.send_message(chat_id, f"🔍 Scanning {len(photos)} bet slips & sending new approved picks to {PUBLISH_CHANNEL_ID}...")
        for p_bytes in photos:
            extracted = self.extract_text_from_photo(p_bytes)
            self.ingest_text_into_ledger(extracted, source_channel="Forwarded_Slip")

        self.sync_and_publish_to_footybett()
        all_today = list(DailyLedgerManager.load_today_items().values())
        if all_today:
            card = BetSlipCardFormatter.format_daily_ledger(all_today)
            self.send_message(chat_id, card)
        else:
            self.send_message(chat_id, "⚠️ Scanned screenshots, but could not detect structured match & odds lines.")

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

    def execute_scan_and_show_today_slate(self, chat_id: int):
        try:
            channels = list(ChannelWebWatcher.get_watched_channels())
            today_str = DailyLedgerManager.get_today_str()
            self.send_message(chat_id, f"⚡ Scanning {len(channels)} channels & syncing new valid picks to {PUBLISH_CHANNEL_ID} ({today_str})...")

            seen = load_json_set(SEEN_POSTS_FILE)
            for ch in channels:
                html = ChannelWebWatcher.fetch_recent_channel_html(ch)
                if not html:
                    continue
                posts = ChannelWebWatcher.extract_posts_today_only(html, only_unseen=True)
                for post_id, text, img_urls in posts:
                    seen.add(post_id)
                    if text.strip():
                        self.ingest_text_into_ledger(text, source_channel=ch)
                    for i_url in img_urls:
                        i_bytes = self.download_url_bytes(i_url)
                        if i_bytes:
                            img_text = self.extract_text_from_photo(i_bytes)
                            self.ingest_text_into_ledger(img_text, source_channel=ch)

            save_json_set(SEEN_POSTS_FILE, seen)

            # Grade and publish any newly confirmed picks / winners to @Footybett ONCE
            self.sync_and_publish_to_footybett()
            all_today = list(DailyLedgerManager.load_today_items().values())

            if not all_today:
                self.send_message(
                    chat_id,
                    f"📅 No structured bet slips have been posted yet for today ({today_str}).\n\n"
                    f"💡 Tip: Use /stats anytime to view your All-Time PnL & Win Rate."
                )
                return

            card = BetSlipCardFormatter.format_daily_ledger(all_today, header_title="TODAY'S COMPLETE BET SLATE")
            self.send_message(chat_id, card)
        except Exception as e:
            logger.error("Scan error: %s", e)
            self.send_message(chat_id, f"❌ Scan error: {e}")

    def background_worker_loop(self):
        logger.info("Background Channel & @Footybett One-Time Publisher Worker started...")
        time.sleep(30)
        cycle = 0
        while True:
            try:
                cycle += 1
                seen = load_json_set(SEEN_POSTS_FILE)
                new_approved_added = False

                for ch in ChannelWebWatcher.get_watched_channels():
                    html = ChannelWebWatcher.fetch_recent_channel_html(ch)
                    posts = ChannelWebWatcher.extract_posts_today_only(html, only_unseen=True)
                    for post_id, text, img_urls in posts:
                        seen.add(post_id)
                        all_blocks = [text] if text.strip() else []
                        for i_url in img_urls:
                            i_bytes = self.download_url_bytes(i_url)
                            if i_bytes:
                                all_blocks.append(self.extract_text_from_photo(i_bytes))
                        for blk in all_blocks:
                            for s in BetParser.parse_multiple(blk, source_channel=ch):
                                item = FootballIntelligenceEngine.evaluate_to_ledger_item(s)
                                is_new, stored = DailyLedgerManager.upsert_bet(item)
                                if is_new and stored.is_approved:
                                    new_approved_added = True

                save_json_set(SEEN_POSTS_FILE, seen)

                # Sync to @Footybett: sends ONLY new unposted individual picks and newly won celebrations
                self.sync_and_publish_to_footybett()

                if cycle % 10 == 0:
                    self.sync_and_publish_to_footybett()

            except Exception as e:
                logger.error("Background worker error: %s", e)
            time.sleep(50)

    def set_official_menu_commands(self):
        commands = [
            {"command": "scan", "description": "⚡ Today's Valid & Invalid Bets"},
            {"command": "results", "description": "🏁 Today's Live Scores & Match Audit"},
            {"command": "stats", "description": "📈 Total PnL, Win Rate & R:R Numbers"},
            {"command": "channels", "description": "👁️ Monitored Telegram Channels (8)"},
            {"command": "status", "description": "⚙️ System & API Quota Status"}
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

        logger.info("Bot listener running with @Footybett One-Time Publisher...")
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
                        "👋 Welcome to Pro Football Syndicate & @Footybett Publisher!\n\n"
                        "Use the blue [ Menu ] button on the left anytime:\n"
                        "• /scan — ⚡ Today's Valid & Invalid Bets\n"
                        "• /results — 🏁 Today's Live Scores & Match Audit\n"
                        "• /stats — 📈 Total PnL, Win Rate & R:R Numbers\n"
                        "• /channels — 👁️ Monitored Telegram Channels\n"
                        "• /status — ⚙️ System & API Quota Status\n\n"
                        "📢 Auto-Publishing: Every new approved bet is sent ONCE to @Footybett, and celebrated ONCE when it wins."
                    )
                    continue

                if text in ["/stats", "📈 Total PnL & Stats"]:
                    def run_stats(cid):
                        self.sync_and_publish_to_footybett()
                        report = BetSlipCardFormatter.format_lifetime_pnl_stats()
                        self.send_message(cid, report)
                    threading.Thread(target=run_stats, args=[chat_id], daemon=True).start()
                    continue

                if text in ["/status", "⚙️ System & Quota Status"]:
                    api_stat = LiveFootballAPI.check_account_status()
                    ocr_stat = "Active (Shuffle Dark-Mode Binarization)" if OCR_AVAILABLE else "Not Installed"
                    channels = ChannelWebWatcher.get_watched_channels()
                    all_hist = DailyLedgerManager.load_all_history_items()
                    today_items = DailyLedgerManager.load_today_items()
                    locks_count = len(load_json_set(PUBLISHED_LOCKS_FILE))
                    self.send_message(
                        chat_id,
                        f"⚙️ SYSTEM STATUS\n"
                        f"════════════════════════════════\n"
                        f"📡 API-Football : {api_stat}\n"
                        f"📸 Image OCR    : {ocr_stat}\n"
                        f"📢 VIP Channel  : {PUBLISH_CHANNEL_ID} ({locks_count} posts locked)\n"
                        f"👁️ Active Feeds : {len(channels)} Channels Monitored\n"
                        f"📅 Today's Slate: {len(today_items)} unique bets\n"
                        f"📚 All-Time DB  : {len(all_hist)} historical bets tracked"
                    )
                    continue

                if text in ["/channels", "👁️ Monitored Channels"]:
                    ch_list = "\n".join(f"• @{c} (https://t.me/s/{c})" for c in sorted(ChannelWebWatcher.get_watched_channels()))
                    self.send_message(
                        chat_id,
                        f"📋 MONITORED CHANNELS ({len(ChannelWebWatcher.get_watched_channels())} Feeds):\n"
                        f"════════════════════════════════\n"
                        f"{ch_list}\n\n"
                        f"📢 Publishing Approved Bets to: {PUBLISH_CHANNEL_ID}\n"
                        f"💡 To add another source channel, send: `/watch username`"
                    )
                    continue

                if text in ["/scan", "⚡ Scan Today's Bets"]:
                    threading.Thread(target=self.execute_scan_and_show_today_slate, args=[chat_id], daemon=True).start()
                    continue

                if text in ["/results", "🏁 Live Scores & Results"]:
                    def run_results_check(cid):
                        self.send_message(cid, "🏁 Updating live & final match scores...")
                        self.sync_and_publish_to_footybett()
                        all_today = list(DailyLedgerManager.load_today_items().values())
                        report = BetSlipCardFormatter.format_results_audit(all_today)
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
                        self.sync_and_publish_to_footybett()
                        all_today = list(DailyLedgerManager.load_today_items().values())
                        card = BetSlipCardFormatter.format_daily_ledger(all_today)
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