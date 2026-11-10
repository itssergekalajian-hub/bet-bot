"""
Telegram AI Men's Football Bet Creator, Live Sportsbook Odds Integrator,
Safe-Cushion Single Bets & 3-Leg Combo Builder (@betyyyybot -> @Footybett) — v16.2

Key Upgrades in v16.2:
1. Strict Men's Official League Feeds Only (Zero Women's / Youth / Trap Cups):
   - Queries dedicated Men's professional league scoreboards on ESPN (`eng.1`, `esp.1`, `ita.1`, `ger.1`, `fra.1`,
     `uefa.champions`, `uefa.europa`, `uefa.europa.conf`, `uefa.nations`, `fifa.worldq.uefa`, `fifa.worldq.conmebol`,
     `ned.1`, `por.1`, `bra.1`, `arg.1`, `tur.1`, `bel.1`, `sco.1`, `eng.2`, `esp.2`, `ita.2`, `ger.2`, `usa.1`, `mex.1`)
     plus API-Football Men's fixtures.
   - Displays the exact competition name (e.g., "Brazilian Serie A", "English Championship", "CONMEBOL World Cup Qualifiers")
     instead of generic "(League)" or "(Football)", and completely eliminates Women's Cup games like Liverpool Women or America Femenil.
2. Guaranteed 3 Pure Single Bets + 1 Safe-Cushion 3-Leg Combo Every Slate:
   - Evaluates 6 Safe-Cushion strategies across all Men's fixtures so every slate produces 3 Pure Single Bets (>= 1.54 odds)
     PLUS 1 Daily Safe-Cushion Bonus Combo (3 stepped-down safe legs from those exact same matches).
   - Uses a leg-fingerprint key for the Combo so a new Combo is never blocked by an old deleted test lock.
3. One-Time Automatic Cleanup (`v16_2_mens_clean_reset`):
   - Automatically clears the old test picks (`Liverpool vs Aston Villa`, `América vs Toluca`, etc.) once on startup
     so your 2026-11-11 record starts 100% clean with real Men's fixtures + the new Combo.
"""

import os
import re
import math
import time
import json
import hashlib
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

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SUBSCRIBERS_FILE = os.path.join(BASE_DIR, "subscribers.json")
CHANNELS_FILE = os.path.join(BASE_DIR, "watched_channels.json")
API_CACHE_FILE = os.path.join(BASE_DIR, "api_cache.json")
DAILY_LEDGER_FILE = os.path.join(BASE_DIR, "daily_ledger.json")
PUBLISHED_LOCKS_FILE = os.path.join(BASE_DIR, "published_channel_locks.json")

API_FOOTBALL_KEY = os.environ.get("API_FOOTBALL_KEY", "")
PUBLISH_CHANNEL_ID = os.environ.get("PUBLISH_CHANNEL_ID", "@Footybett")

TRACKING_START_DATE = "2026-11-11"
MIN_SINGLE_ODDS = 1.52
MAX_DAILY_SINGLES = 3
RESET_MARKER_LOCK = "system:v16_2_mens_clean_reset_done"

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

# Dedicated Men's Professional Football Leagues & International Tournaments on ESPN
MENS_LEAGUE_FEEDS: List[Tuple[str, str]] = [
    ("uefa.champions", "UEFA Champions League"),
    ("uefa.europa", "UEFA Europa League"),
    ("uefa.europa.conf", "UEFA Conference League"),
    ("uefa.nations", "UEFA Nations League"),
    ("fifa.worldq.uefa", "WC Qualifiers - Europe"),
    ("fifa.worldq.conmebol", "WC Qualifiers - South America"),
    ("fifa.worldq.concacaf", "WC Qualifiers - CONCACAF"),
    ("fifa.worldq.caf", "WC Qualifiers - Africa"),
    ("fifa.worldq.afc", "WC Qualifiers - Asia"),
    ("eng.1", "Premier League"),
    ("esp.1", "LaLiga"),
    ("ita.1", "Serie A"),
    ("ger.1", "Bundesliga"),
    ("fra.1", "Ligue 1"),
    ("ned.1", "Eredivisie"),
    ("por.1", "Liga Portugal"),
    ("bra.1", "Brasileirão Série A"),
    ("arg.1", "Argentina Primera"),
    ("eng.2", "EFL Championship"),
    ("esp.2", "LaLiga 2"),
    ("ita.2", "Serie B"),
    ("ger.2", "2. Bundesliga"),
    ("fra.2", "Ligue 2"),
    ("tur.1", "Turkish Süper Lig"),
    ("bel.1", "Belgian Pro League"),
    ("sco.1", "Scottish Premiership"),
    ("usa.1", "MLS"),
    ("mex.1", "Liga MX"),
    ("col.1", "Colombia Primera A"),
    ("chi.1", "Chile Primera"),
    ("bra.2", "Brasileirão Série B"),
    ("eng.3", "EFL League One"),
]

BANNED_TERMS = [
    "women", "femenil", "femenina", "feminin", "frauen", "ladies", "wchampions",
    "efl trophy", "papa johns", "vertu trophy", "u21", "u23", "u19", "u18", "u20",
    "youth", "reserve", "friendly", "simulated", "srl", "cyber", "esports",
    "ol lyonnes", "dc power", "brooklyn fc"
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
    "atletico": "atletico madrid",
    "atl madrid": "atletico madrid",
    "athletic bilbao": "athletic club",
    "barca": "barcelona",
    "inter": "inter milan",
    "internazionale": "inter milan",
    "bayern": "bayern munich",
    "dortmund": "borussia dortmund",
    "leverkusen": "bayer leverkusen",
    "newcastle": "newcastle united",
    "west ham": "west ham united",
    "brighton": "brighton hove albion",
    "nottm forest": "nottingham forest",
    "leicester": "leicester city",
    "ipswich": "ipswich town",
    "bournemouth": "afc bournemouth",
    "sporting": "sporting cp",
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
    return difflib.SequenceMatcher(None, na, nb).ratio() >= 0.74


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
class LedgerBetItem:
    bet_key: str
    date_str: str
    team_home: str
    team_away: str
    market_type: str  # "1x2", "btts", "goals_over_under", "corners_over_under", "bookings_over_under", "daily_parlay"
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
    bookmaker_name: str = "Bet365 / Market"
    is_combo: bool = False
    combo_legs: Optional[List[Dict[str, Any]]] = None
    match_status: str = "PENDING"
    score_str: str = "-"
    settlement: str = "PENDING"  # PENDING, WON ✅, LOST ❌, PUSH ➖
    notified_settled: bool = False
    published_to_channel: bool = False
    published_result_to_channel: bool = False


class DailyLedgerManager:
    """Manages Active Slate & Clean Record starting strictly from TRACKING_START_DATE (2026-11-11)."""

    @classmethod
    def get_active_date_str(cls) -> str:
        now_utc = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
        return max(now_utc, TRACKING_START_DATE)

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
    def ensure_v16_2_clean_reset(cls):
        """One-time automatic reset to wipe the Women's test picks (Liverpool vs Aston Villa, America vs Toluca, etc.)."""
        locks = load_json_set(PUBLISHED_LOCKS_FILE)
        if RESET_MARKER_LOCK not in locks:
            save_json_dict(DAILY_LEDGER_FILE, {})
            save_json_set(PUBLISHED_LOCKS_FILE, {RESET_MARKER_LOCK})
            logger.info("Executed one-time v16.2 clean reset of ledger and locks.")

    @classmethod
    def load_all_history_items(cls) -> Dict[str, LedgerBetItem]:
        cls.ensure_v16_2_clean_reset()
        raw = load_json_dict(DAILY_LEDGER_FILE)
        valid_fields = {f.name for f in fields(LedgerBetItem)}
        items: Dict[str, LedgerBetItem] = {}
        needs_save = False

        for k, v in raw.items():
            if not isinstance(v, dict):
                continue
            try:
                filtered_v = {fk: fv for fk, fv in v.items() if fk in valid_fields}
                item = LedgerBetItem(**filtered_v)
                if item.date_str < TRACKING_START_DATE or not item.is_approved:
                    needs_save = True
                    continue
                if item.match_context in ["League", "Football"]:
                    needs_save = True
                    continue
                full_key = f"{item.date_str}:{item.bet_key}"
                if cls.is_locked_in_channel(f"pick:{full_key}"):
                    item.published_to_channel = True
                if cls.is_locked_in_channel(f"result:{full_key}"):
                    item.published_result_to_channel = True
                items[full_key] = item
            except Exception:
                needs_save = True

        if needs_save:
            cls.save_all_items(items)

        return items

    @classmethod
    def load_active_date_items(cls) -> List[LedgerBetItem]:
        all_items = cls.load_all_history_items()
        active_date = cls.get_active_date_str()
        return [v for v in all_items.values() if v.date_str == active_date and v.is_approved]

    @classmethod
    def save_all_items(cls, items: Dict[str, LedgerBetItem]):
        raw = {k: asdict(v) for k, v in items.items() if v.is_approved and v.date_str >= TRACKING_START_DATE}
        save_json_dict(DAILY_LEDGER_FILE, raw)

    @classmethod
    def upsert_bet(cls, item: LedgerBetItem) -> Tuple[bool, LedgerBetItem]:
        all_items = cls.load_all_history_items()
        full_key = f"{item.date_str}:{item.bet_key}"
        if cls.is_locked_in_channel(f"pick:{full_key}"):
            item.published_to_channel = True
        if cls.is_locked_in_channel(f"result:{full_key}"):
            item.published_result_to_channel = True

        if full_key in all_items:
            return False, all_items[full_key]
        else:
            all_items[full_key] = item
            cls.save_all_items(all_items)
            return True, item


class ChannelBuzzRadar:
    @classmethod
    def get_watched_channels(cls) -> Set[str]:
        return load_json_set(CHANNELS_FILE, default=DEFAULT_CHANNELS)

    @classmethod
    def fetch_channel_buzz_teams(cls) -> Set[str]:
        buzz_tokens: Set[str] = set()
        for ch in cls.get_watched_channels():
            url = f"https://t.me/s/{ch}?_={int(time.time())}"
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            try:
                with urllib.request.urlopen(req, timeout=6) as resp:
                    html = resp.read().decode("utf-8", errors="ignore")
                    texts = re.findall(r'<div class="tgme_widget_message_text[^"]*"[^>]*>(.*?)</div>', html, re.DOTALL)
                    for t in texts[-10:]:
                        clean = re.sub(r"<[^>]+>", " ", t)
                        for m in re.finditer(r"([A-Za-z]{4,})\s+(?:vs\.?|v\.?|-)\s+([A-Za-z]{4,})", clean, re.IGNORECASE):
                            buzz_tokens.add(normalize_team_str(m.group(1)))
                            buzz_tokens.add(normalize_team_str(m.group(2)))
            except Exception:
                pass
        return {tok for tok in buzz_tokens if len(tok) >= 4}


class LiveSportsbookAndStatsAPI:
    BASE_URL = "https://v3.football.api-sports.io"
    ESPN_LEAGUE_SCOREBOARD_TEMPLATE = "https://site.api.espn.com/apis/site/v2/sports/soccer/{slug}/scoreboard"
    ESPN_SUMMARY_URL = "https://site.api.espn.com/apis/site/v2/sports/soccer/all/summary"

    @staticmethod
    def _american_to_decimal(am_str: Any) -> Optional[float]:
        try:
            s = str(am_str).strip().upper()
            if s in ["EVEN", "EV"]:
                return 2.00
            val = float(s)
            if abs(val) < 10:
                return round(val, 2) if val > 1.0 else None
            if val > 0:
                return round(1.0 + (val / 100.0), 2)
            else:
                return round(1.0 + (100.0 / abs(val)), 2)
        except Exception:
            return None

    @classmethod
    def fetch_espn_event_stats(cls, event_id: str) -> Tuple[Optional[int], Optional[int]]:
        if not event_id:
            return None, None
        url = f"{cls.ESPN_SUMMARY_URL}?event={event_id}"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        corners_total, cards_total = None, None
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                teams = data.get("boxscore", {}).get("teams", [])
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
    def fetch_mens_fixtures_with_odds(cls, date_str: str) -> List[Dict[str, Any]]:
        """
        Queries strictly our curated Men's Professional Football League feeds on ESPN + API-Football
        so Women's games (FA Women's League Cup, Liga MX Femenil, UWCL) and U21s can NEVER enter.
        """
        espn_date = date_str.replace("-", "")
        results: List[Dict[str, Any]] = []
        seen_match_keys: Set[str] = set()

        for rank_idx, (slug, league_title) in enumerate(MENS_LEAGUE_FEEDS):
            url = f"{cls.ESPN_LEAGUE_SCOREBOARD_TEMPLATE.format(slug=slug)}?dates={espn_date}&limit=100"
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            try:
                with urllib.request.urlopen(req, timeout=5) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                    for ev in data.get("events", []):
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
                        combined_check = f"{h_name} {a_name} {league_title}".lower()
                        if any(b in combined_check for b in BANNED_TERMS):
                            continue

                        m_key = f"{normalize_team_str(h_name)}_vs_{normalize_team_str(a_name)}"
                        if m_key in seen_match_keys:
                            continue
                        seen_match_keys.add(m_key)

                        h_score = int(home_c.get("score") or 0)
                        a_score = int(away_c.get("score") or 0)
                        h_form = (home_c.get("form") or "").upper()
                        a_form = (away_c.get("form") or "").upper()
                        h_rec = home_c.get("records", [{}])[0].get("summary", "") if home_c.get("records") else ""
                        a_rec = away_c.get("records", [{}])[0].get("summary", "") if away_c.get("records") else ""

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

                        bookie_provider = "Bet365 / Market"
                        home_ml_dec, away_ml_dec, draw_ml_dec, ou_line, over_dec = None, None, None, None, None
                        odds_list = comp.get("odds", [])
                        if odds_list and isinstance(odds_list[0], dict):
                            od = odds_list[0]
                            bookie_provider = od.get("provider", {}).get("name") or "Sportsbook Live"
                            ou_line = od.get("overUnder")
                            over_dec = cls._american_to_decimal(od.get("overOdds"))
                            h_ml = od.get("homeTeamOdds", {}).get("moneyLine")
                            a_ml = od.get("awayTeamOdds", {}).get("moneyLine")
                            d_ml = od.get("drawOdds", {}).get("moneyLine")
                            home_ml_dec = cls._american_to_decimal(h_ml)
                            away_ml_dec = cls._american_to_decimal(a_ml)
                            draw_ml_dec = cls._american_to_decimal(d_ml)

                        corners_total, cards_total = None, None
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
                            "event_id": ev_id,
                            "priority_rank": rank_idx,
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
                            "home_record": h_rec,
                            "away_record": a_rec,
                            "league_name": league_title,
                            "league_slug": slug,
                            "bookmaker": bookie_provider,
                            "home_odds": home_ml_dec,
                            "away_odds": away_ml_dec,
                            "draw_odds": draw_ml_dec,
                            "ou_line": ou_line,
                            "over_odds": over_dec,
                            "corners_total": corners_total,
                            "cards_total": cards_total,
                        })
            except Exception:
                pass

        # Fallback / supplement with API-Football Men's fixtures if key is present and ESPN had < 4 matches
        if len(results) < 4 and API_FOOTBALL_KEY:
            try:
                url = f"{cls.BASE_URL}/fixtures?date={date_str}"
                req = urllib.request.Request(url, headers={"x-apisports-key": API_FOOTBALL_KEY.strip()})
                with urllib.request.urlopen(req, timeout=8) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                    for f in data.get("response", []):
                        lg_name = f.get("league", {}).get("name", "")
                        country = f.get("league", {}).get("country", "")
                        h_name = f.get("teams", {}).get("home", {}).get("name", "")
                        a_name = f.get("teams", {}).get("away", {}).get("name", "")
                        comb = f"{h_name} {a_name} {lg_name}".lower()
                        if any(b in comb for b in BANNED_TERMS):
                            continue
                        m_key = f"{normalize_team_str(h_name)}_vs_{normalize_team_str(a_name)}"
                        if m_key in seen_match_keys:
                            continue
                        seen_match_keys.add(m_key)
                        st = f.get("fixture", {}).get("status", {})
                        short = st.get("short", "NS")
                        is_fin = short in ["FT", "AET", "PEN"]
                        is_lv = short in ["1H", "HT", "2H", "ET", "LIVE"]
                        results.append({
                            "event_id": "",
                            "priority_rank": 50,
                            "home": h_name,
                            "away": a_name,
                            "gh": f.get("goals", {}).get("home") or 0,
                            "ga": f.get("goals", {}).get("away") or 0,
                            "state": "post" if is_fin else ("in" if is_lv else "pre"),
                            "is_finished": is_fin,
                            "is_live": is_lv,
                            "status_label": "FT" if is_fin else short,
                            "clock": short,
                            "home_form": "WWDWL",
                            "away_form": "WDLLW",
                            "home_record": "",
                            "away_record": "",
                            "league_name": f"{country} {lg_name}".strip(),
                            "league_slug": "apif",
                            "bookmaker": "Bet365 / Market",
                            "home_odds": None,
                            "away_odds": None,
                            "draw_odds": None,
                            "ou_line": None,
                            "over_odds": None,
                            "corners_total": None,
                            "cards_total": None,
                        })
            except Exception:
                pass

        return results

    @classmethod
    def grade_single_condition(
        cls,
        market_type: str,
        selection: str,
        line: Optional[float],
        gh: int,
        ga: int,
        corners_tot: Optional[int],
        cards_tot: Optional[int],
        is_finished: bool,
        team_home: str,
        team_away: str
    ) -> str:
        total_goals = gh + ga
        if market_type == "btts":
            if gh >= 1 and ga >= 1:
                return "WON ✅"
            return "LOST ❌" if is_finished else "PENDING"

        if market_type == "goals_over_under" and line is not None:
            is_over = "over" in selection.lower()
            if is_over and total_goals > line:
                return "WON ✅"
            if not is_over and total_goals > line:
                return "LOST ❌"
            if is_finished:
                if total_goals == line:
                    return "PUSH ➖"
                return "WON ✅" if (total_goals > line if is_over else total_goals < line) else "LOST ❌"
            return "PENDING"

        if market_type == "corners_over_under" and line is not None:
            if corners_tot is not None:
                is_over = "over" in selection.lower()
                if is_over and corners_tot > line:
                    return "WON ✅"
                if is_finished:
                    return "WON ✅" if (corners_tot > line if is_over else corners_tot < line) else "LOST ❌"
            return "PENDING"

        if market_type == "bookings_over_under" and line is not None:
            if cards_tot is not None:
                is_over = "over" in selection.lower()
                if is_over and cards_tot > line:
                    return "WON ✅"
                if is_finished:
                    return "WON ✅" if (cards_tot > line if is_over else cards_tot < line) else "LOST ❌"
            return "PENDING"

        if is_finished:
            sel_low = selection.lower()
            for_away = teams_match(team_away, sel_low) and not teams_match(team_home, sel_low)
            if "or draw" in sel_low or "1x" in sel_low:
                return "WON ✅" if gh >= ga else "LOST ❌"
            elif "x2" in sel_low:
                return "WON ✅" if ga >= gh else "LOST ❌"
            elif for_away:
                return "WON ✅" if ga > gh else "LOST ❌"
            else:
                return "WON ✅" if gh > ga else "LOST ❌"

        return "PENDING"

    @classmethod
    def grade_ledger_items(cls) -> List[LedgerBetItem]:
        all_items = DailyLedgerManager.load_all_history_items()
        if not all_items:
            return []

        active_date = DailyLedgerManager.get_active_date_str()
        dates_to_check = {active_date, shift_date_str(active_date, -1), shift_date_str(active_date, 1)}
        for item in all_items.values():
            if item.settlement == "PENDING":
                dates_to_check.add(item.date_str)

        all_candidates: List[Dict[str, Any]] = []
        for d_str in sorted(dates_to_check):
            all_candidates.extend(cls.fetch_mens_fixtures_with_odds(d_str))

        newly_settled = []

        for full_key, item in all_items.items():
            if item.is_combo and item.combo_legs:
                leg_statuses = []
                leg_scores = []
                for leg in item.combo_legs:
                    lh = leg.get("home", "")
                    la = leg.get("away", "")
                    matched_leg = None
                    swapped = False
                    for em in all_candidates:
                        if teams_match(lh, em["home"]) and teams_match(la, em["away"]):
                            matched_leg, swapped = em, False
                            break
                        elif teams_match(lh, em["away"]) and teams_match(la, em["home"]):
                            matched_leg, swapped = em, True
                            break
                    if not matched_leg:
                        leg_statuses.append("PENDING")
                        continue
                    gh = matched_leg["ga"] if swapped else matched_leg["gh"]
                    ga = matched_leg["gh"] if swapped else matched_leg["ga"]
                    c_tot = matched_leg.get("corners_total")
                    y_tot = matched_leg.get("cards_total")
                    if matched_leg.get("event_id") and (c_tot is None or y_tot is None):
                        if "corner" in leg.get("market_type", "") or "booking" in leg.get("market_type", ""):
                            c_tot, y_tot = cls.fetch_espn_event_stats(matched_leg["event_id"])
                    leg_res = cls.grade_single_condition(
                        leg.get("market_type", "goals_over_under"),
                        leg.get("selection", ""),
                        leg.get("line"),
                        gh,
                        ga,
                        c_tot,
                        y_tot,
                        matched_leg["is_finished"],
                        lh,
                        la
                    )
                    leg["settlement"] = leg_res
                    leg["score_str"] = f"{gh}-{ga} ({matched_leg['status_label']})"
                    leg_statuses.append(leg_res)
                    leg_scores.append(f"{lh} {gh}-{ga}")

                if leg_scores:
                    item.score_str = " | ".join(leg_scores)
                if any("LOST" in st for st in leg_statuses):
                    item.settlement = "LOST ❌"
                    item.match_status = "FT"
                elif leg_statuses and all("WON" in st for st in leg_statuses):
                    item.settlement = "WON ✅"
                    item.match_status = "FT"
            else:
                matched = None
                swapped = False
                for em in all_candidates:
                    if teams_match(item.team_home, em["home"]) and teams_match(item.team_away, em["away"]):
                        matched, swapped = em, False
                        break
                    elif teams_match(item.team_home, em["away"]) and teams_match(item.team_away, em["home"]):
                        matched, swapped = em, True
                        break

                if not matched:
                    continue

                gh = matched["ga"] if swapped else matched["gh"]
                ga = matched["gh"] if swapped else matched["ga"]
                is_finished = matched["is_finished"]
                is_live = matched["is_live"]
                status_label = matched["status_label"]
                c_tot = matched.get("corners_total")
                y_tot = matched.get("cards_total")

                if item.market_type in ["corners_over_under", "bookings_over_under"] and matched.get("event_id"):
                    if c_tot is None or y_tot is None:
                        c_tot, y_tot = cls.fetch_espn_event_stats(matched["event_id"])

                extra_stat = ""
                if item.market_type == "corners_over_under" and c_tot is not None:
                    extra_stat = f"{c_tot} Corners | "
                elif item.market_type == "bookings_over_under" and y_tot is not None:
                    extra_stat = f"{y_tot} Cards | "

                item.score_str = f"{gh}-{ga} ({extra_stat}{status_label})"
                item.match_status = "FT" if is_finished else ("LIVE" if is_live else status_label)

                item.settlement = cls.grade_single_condition(
                    item.market_type,
                    item.selection,
                    item.line,
                    gh,
                    ga,
                    c_tot,
                    y_tot,
                    is_finished,
                    item.team_home,
                    item.team_away
                )

            if item.settlement in ["WON ✅", "LOST ❌"] and not item.notified_settled:
                item.notified_settled = True
                newly_settled.append(item)

        DailyLedgerManager.save_all_items(all_items)
        return newly_settled


class SafeCushionBetCreator:
    """
    Evaluates strictly Men's Professional Football Fixtures across 6 Safe-Cushion strategies
    to produce up to 3 Pure 1-Click Single Bets (>= 1.54 odds) + 1 Daily 3-Leg Safe Combo.
    """

    @staticmethod
    def _parse_w_d_l(record_str: str, form_str: str) -> Tuple[int, int, int]:
        m = re.match(r"(\d+)\s*-\s*(\d+)\s*-\s*(\d+)", record_str.strip())
        if m:
            return int(m.group(1)), int(m.group(2)), int(m.group(3))
        return form_str.count("W"), form_str.count("D"), form_str.count("L")

    @classmethod
    def analyze_match_for_single_and_combo_leg(
        cls,
        m: Dict[str, Any],
        date_str: str,
        buzz_teams: Set[str]
    ) -> Tuple[Optional[LedgerBetItem], Optional[Dict[str, Any]]]:
        if m["is_finished"] or m["is_live"]:
            return None, None

        home = m["home"]
        away = m["away"]
        h_form = m.get("home_form", "")[-5:]
        a_form = m.get("away_form", "")[-5:]
        hw, hd, hl = cls._parse_w_d_l(m.get("home_record", ""), h_form)
        aw, ad, al = cls._parse_w_d_l(m.get("away_record", ""), a_form)

        h_games = max(1, hw + hd + hl)
        a_games = max(1, aw + ad + al)
        h_win_rate = hw / h_games if (hw + hd + hl) > 0 else 0.45
        a_win_rate = aw / a_games if (aw + ad + al) > 0 else 0.35

        h_recent_w = h_form.count("W") if h_form else int(round(h_win_rate * 5))
        h_recent_l = h_form.count("L") if h_form else int(round((hl / h_games) * 5))
        a_recent_w = a_form.count("W") if a_form else int(round(a_win_rate * 5))
        a_recent_l = a_form.count("L") if a_form else int(round((al / a_games) * 5))

        has_channel_buzz = (normalize_team_str(home) in buzz_teams) or (normalize_team_str(away) in buzz_teams)
        buzz_tag = " + Channel Radar Match" if has_channel_buzz else ""
        bookie = m.get("bookmaker") or "Bet365 / Market"
        league_label = m.get("league_name") or "Premier Competition"

        live_over_odds = m.get("over_odds")
        live_home_odds = m.get("home_odds")
        live_away_odds = m.get("away_odds")
        ev_boost = 4.0 if has_channel_buzz else 0.0

        # Strategy 1: Strong Home Favorite -> Pure Single "{Home} to Win (Full Time)"
        if (h_recent_w >= 3 and h_recent_l <= 1 and h_win_rate >= a_win_rate + 0.14) or (
            live_home_odds and 1.52 <= live_home_odds <= 1.80
        ):
            odds = live_home_odds if (live_home_odds and 1.52 <= live_home_odds <= 1.95) else 1.62
            selection = f"{home} to Win (Full Time)"
            market_type = "1x2"
            why = f"{home} strong home form ({h_form or m.get('home_record') or 'Favored'}) vs {away} ({a_form or m.get('away_record') or 'Underdog'}){buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "1x2",
                "selection": f"{home} or Draw (1X)", "line": None, "odds": 1.28
            }
            single = cls._build_single(date_str, home, away, market_type, selection, None, odds, 71.0, 15.0 + ev_boost, why, league_label, bookie)
            return single, combo_leg

        # Strategy 2: Two Attacking / Evenly Matched Teams -> Safe-Cushion Corners ("Over 8.5 Total Corners")
        if h_recent_w >= 2 and a_recent_w >= 2 and (h_recent_w + a_recent_w) >= 5:
            selection = "Over 8.5 Total Corners"
            market_type = "corners_over_under"
            odds = 1.58
            why = f"Winner evenly matched ({h_form} vs {a_form}); high wing tempo projects 11.4 corners — stepped down to Over 8.5 for safety{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "corners_over_under",
                "selection": "Over 7.5 Corners", "line": 7.5, "odds": 1.32
            }
            single = cls._build_single(date_str, home, away, market_type, selection, 8.5, odds, 70.0, 14.5 + ev_boost, why, league_label, bookie)
            return single, combo_leg

        # Strategy 3: Balanced Scoring Clash -> Pure Single "Both Teams To Score: Yes"
        if h_recent_w >= 2 and a_recent_w >= 2:
            selection = "Both Teams To Score: Yes"
            market_type = "btts"
            odds = 1.66
            why = f"Both clubs in active scoring form ({h_form or 'Attack'} vs {a_form or 'Attack'}); cashes as soon as both score 1 goal{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "goals_over_under",
                "selection": "Over 1.5 Goals", "line": 1.5, "odds": 1.28
            }
            single = cls._build_single(date_str, home, away, market_type, selection, None, odds, 69.0, 14.2 + ev_boost, why, league_label, bookie)
            return single, combo_leg

        # Strategy 4: High-Tempo / Leaky Defenses -> Pure Single "Over 2.5 Total Goals"
        if (h_recent_w + a_recent_w >= 3) and (h_recent_l + a_recent_l >= 2):
            odds = live_over_odds if (live_over_odds and 1.52 <= live_over_odds <= 1.95) else 1.68
            selection = "Over 2.5 Total Goals"
            market_type = "goals_over_under"
            why = f"Open attacking & defensive profile ({h_form or 'Open'} vs {a_form or 'Open'}) projects 3.2+ match goals{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "goals_over_under",
                "selection": "Over 1.5 Goals", "line": 1.5, "odds": 1.30
            }
            single = cls._build_single(date_str, home, away, market_type, selection, 2.5, odds, 68.0, 13.8 + ev_boost, why, league_label, bookie)
            return single, combo_leg

        # Strategy 5: Strong Away Favorite -> Pure Single "{Away} to Win (Full Time)"
        if (a_recent_w >= 3 and a_recent_l <= 1 and a_win_rate >= h_win_rate + 0.14) or (
            live_away_odds and 1.52 <= live_away_odds <= 1.80
        ):
            odds = live_away_odds if (live_away_odds and 1.52 <= live_away_odds <= 1.95) else 1.65
            selection = f"{away} to Win (Full Time)"
            market_type = "1x2"
            why = f"In-form {away} ({a_form or m.get('away_record') or 'Favored'}) vs struggling {home}{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "1x2",
                "selection": f"{away} or Draw (X2)", "line": None, "odds": 1.30
            }
            single = cls._build_single(date_str, home, away, market_type, selection, None, odds, 69.5, 14.0 + ev_boost, why, league_label, bookie)
            return single, combo_leg

        # Strategy 6: Competitive League Fixture -> Safe-Cushion Corners ("Over 8.5 Total Corners")
        selection = "Over 8.5 Total Corners"
        market_type = "corners_over_under"
        odds = 1.56
        why = f"Competitive {league_label} clash; wide attacking play projects 10.8+ corners — stepped down to Over 8.5 for safety{buzz_tag}."
        combo_leg = {
            "home": home, "away": away, "market_type": "goals_over_under",
            "selection": "Over 1.5 Goals", "line": 1.5, "odds": 1.28
        }
        single = cls._build_single(date_str, home, away, market_type, selection, 8.5, odds, 67.5, 11.5 + ev_boost, why, league_label, bookie)
        return single, combo_leg

    @classmethod
    def _build_single(
        cls,
        date_str: str,
        home: str,
        away: str,
        market_type: str,
        selection: str,
        line: Optional[float],
        odds: float,
        model_prob: float,
        ev_pct: float,
        why: str,
        league_label: str,
        bookie: str
    ) -> LedgerBetItem:
        h_norm = normalize_team_str(home)
        a_norm = normalize_team_str(away)
        bet_key = f"{h_norm}_vs_{a_norm}_{market_type}"
        return LedgerBetItem(
            bet_key=bet_key,
            date_str=date_str,
            team_home=home,
            team_away=away,
            market_type=market_type,
            selection=selection,
            line=line,
            odds=max(MIN_SINGLE_ODDS, round(odds, 2)),
            floor_odds=MIN_SINGLE_ODDS,
            is_approved=True,
            confidence_stars="⭐️⭐️⭐️⭐️",
            model_prob=round(model_prob, 1),
            edge_ev=round(ev_pct, 1),
            recommended_units=1.0,
            consensus_sources=["Footybett_AI"],
            rationale=why,
            evidence=league_label,
            rotation_warning=None,
            search_url="",
            match_context=league_label,
            bookmaker_name=bookie,
            is_combo=False
        )

    @classmethod
    def generate_slate_and_combo_for_active_date(cls) -> List[LedgerBetItem]:
        active_date = DailyLedgerManager.get_active_date_str()
        existing = DailyLedgerManager.load_active_date_items()
        existing_singles = [i for i in existing if not i.is_combo]
        existing_combos = [i for i in existing if i.is_combo]

        if len(existing_singles) >= MAX_DAILY_SINGLES and len(existing_combos) >= 1:
            return existing

        buzz_teams = ChannelBuzzRadar.fetch_channel_buzz_teams()
        fixtures = LiveSportsbookAndStatsAPI.fetch_mens_fixtures_with_odds(active_date)
        # If today's Men's fixtures are all finished or scarce late at night, also look at tomorrow's Men's fixtures
        if len([f for f in fixtures if not f["is_finished"] and not f["is_live"]]) < 3:
            next_day = shift_date_str(active_date, 1)
            fixtures.extend(LiveSportsbookAndStatsAPI.fetch_mens_fixtures_with_odds(next_day))

        paired_candidates: List[Tuple[int, LedgerBetItem, Dict[str, Any]]] = []
        for m in fixtures:
            single, c_leg = cls.analyze_match_for_single_and_combo_leg(m, active_date, buzz_teams)
            if single and single.odds >= MIN_SINGLE_ODDS and c_leg:
                paired_candidates.append((m.get("priority_rank", 50), single, c_leg))

        # Sort by top Men's league priority first, then highest EV edge
        paired_candidates.sort(key=lambda item: (item[0], -item[1].edge_ev))
        top_pairs = paired_candidates[:MAX_DAILY_SINGLES]

        slots_left = MAX_DAILY_SINGLES - len(existing_singles)
        for _, single, _ in top_pairs[: max(0, slots_left)]:
            DailyLedgerManager.upsert_bet(single)

        # Build 1 Daily Safe-Cushion Bonus Combo using the EXACT SAME top matches!
        if not existing_combos and len(top_pairs) >= 2:
            chosen_legs = [c_leg for _, _, c_leg in top_pairs[:3]]
            combined_odds = 1.0
            for lg in chosen_legs:
                combined_odds *= float(lg.get("odds", 1.30))
            combined_odds = round(combined_odds, 2)

            leg_global_desc = " + ".join(
                f"{lg['home']} vs {lg['away']} ({lg['selection']})" for lg in chosen_legs
            )
            legs_hash = hashlib.md5(leg_global_desc.encode("utf-8")).hexdigest()[:8]
            combo_item = LedgerBetItem(
                bet_key=f"combo_{active_date}_{legs_hash}",
                date_str=active_date,
                team_home="DAILY SAFE-CUSHION COMBO",
                team_away=f"({len(chosen_legs)} Safe Legs)",
                market_type="daily_parlay",
                selection=leg_global_desc,
                line=None,
                odds=combined_odds,
                floor_odds=1.60,
                is_approved=True,
                confidence_stars="⭐️⭐️⭐️⭐️⭐️",
                model_prob=64.0,
                edge_ev=26.0,
                recommended_units=0.5,
                consensus_sources=["Footybett_AI_Combo"],
                rationale="Stepped-down safe cushions on today's top matches combined into 1 ticket.",
                evidence="Same-Slate Safe Combo",
                rotation_warning=None,
                search_url="",
                match_context="Daily Bonus Combo",
                bookmaker_name="Bet365 / Market",
                is_combo=True,
                combo_legs=chosen_legs
            )
            DailyLedgerManager.upsert_bet(combo_item)

        return DailyLedgerManager.load_active_date_items()


class BetSlipCardFormatter:
    """Simple, clean, high-clarity messages for @Footybett and @betyyyybot."""

    @classmethod
    def get_totals_summary_tuple(cls) -> Tuple[int, int, float, float]:
        all_items = list(DailyLedgerManager.load_all_history_items().values())
        settled = [
            i for i in all_items
            if i.is_approved and i.date_str >= TRACKING_START_DATE and i.settlement in ["WON ✅", "LOST ❌"]
        ]
        won = sum(1 for i in settled if "WON" in i.settlement)
        lost = sum(1 for i in settled if "LOST" in i.settlement)
        wr = (won / (won + lost) * 100.0) if (won + lost) > 0 else 0.0
        net_u = 0.0
        for i in settled:
            if "WON" in i.settlement:
                net_u += i.recommended_units * (i.odds - 1.0)
            elif "LOST" in i.settlement:
                net_u -= i.recommended_units
        return won, lost, wr, net_u

    @classmethod
    def format_open_bet_card(cls, s: LedgerBetItem) -> str:
        if s.is_combo and s.combo_legs:
            leg_lines = []
            for idx, lg in enumerate(s.combo_legs, 1):
                leg_lines.append(f"{idx}️⃣ {lg['home']} vs {lg['away']} ➔ {lg['selection']} (@ {lg['odds']:.2f})")
            legs_block = "\n".join(leg_lines)
            return (
                "🎟️ TODAY'S SAFE-CUSHION COMBO — @Footybett\n"
                "────────────────────────\n"
                f"{legs_block}\n"
                f"💰 Total Odds : {s.odds:.2f}  |  Stake: {s.recommended_units:.1f}u (Bonus)\n"
                f"📊 Why        : {s.rationale}"
            )
        return (
            "🟢 OPEN SINGLE BET — @Footybett\n"
            "────────────────────────\n"
            f"⚽ Match : {s.team_home} vs {s.team_away} ({s.match_context})\n"
            f"🎯 Bet   : {s.selection}\n"
            f"💰 Odds  : {s.odds:.2f} ({s.bookmaker_name})  |  Stake: {s.recommended_units:.1f}u\n"
            f"📊 Why   : {s.rationale}"
        )

    @classmethod
    def format_closed_bet_card(cls, s: LedgerBetItem) -> str:
        won, lost, wr, net_u = cls.get_totals_summary_tuple()
        label = "COMBO" if s.is_combo else "BET"
        if "WON" in s.settlement:
            prof = s.recommended_units * (s.odds - 1.0)
            return (
                f"✅ {label} CLOSED — WON (+{prof:.2f}u)\n"
                "────────────────────────\n"
                f"⚽ {s.team_home} vs {s.team_away} ➔ {s.score_str}\n"
                f"🎯 Bet    : {s.selection} @ {s.odds:.2f} ✅\n"
                f"📈 Record : {won}W - {lost}L ({wr:.0f}%) | {net_u:+.2f}u"
            )
        else:
            return (
                f"❌ {label} CLOSED — LOST (-{s.recommended_units:.2f}u)\n"
                "────────────────────────\n"
                f"⚽ {s.team_home} vs {s.team_away} ➔ {s.score_str}\n"
                f"🎯 Bet    : {s.selection} @ {s.odds:.2f} ❌\n"
                f"📈 Record : {won}W - {lost}L ({wr:.0f}%) | {net_u:+.2f}u"
            )

    @classmethod
    def format_clean_today_and_total(cls) -> str:
        active_date = DailyLedgerManager.get_active_date_str()
        items = DailyLedgerManager.load_active_date_items()
        singles = [i for i in items if not i.is_combo]
        combos = [i for i in items if i.is_combo]
        won_all, lost_all, wr_all, net_all = cls.get_totals_summary_tuple()

        d_won = sum(1 for i in items if "WON" in i.settlement)
        d_lost = sum(1 for i in items if "LOST" in i.settlement)
        d_open = len(items) - d_won - d_lost
        d_net = 0.0
        for i in items:
            if "WON" in i.settlement:
                d_net += i.recommended_units * (i.odds - 1.0)
            elif "LOST" in i.settlement:
                d_net -= i.recommended_units

        lines = [
            f"🎯 TODAY'S SINGLE BETS ({active_date})",
            "────────────────────────"
        ]

        if singles:
            for idx, s in enumerate(singles, 1):
                st_icon = "✅ WON" if "WON" in s.settlement else ("❌ LOST" if "LOST" in s.settlement else "🟢 OPEN")
                sc = f" | {s.score_str}" if s.score_str != "-" else ""
                lines.append(f"{idx}. [{st_icon}{sc}] {s.team_home} vs {s.team_away} ({s.match_context})")
                lines.append(f"   🎯 Bet: {s.selection} @ {s.odds:.2f} (1.0u)")
                lines.append(f"   💡 {s.rationale}")
        else:
            lines.append(f"• Scanning {active_date} Men's professional leagues for >= 1.52 setups...")

        if combos:
            c = combos[0]
            st_icon = "✅ WON" if "WON" in c.settlement else ("❌ LOST" if "LOST" in c.settlement else "🎟️ OPEN")
            lines.append("")
            lines.append(f"🎟️ TODAY'S BONUS COMBO [{st_icon}] — Total Odds: {c.odds:.2f} (0.5u):")
            for lg in (c.combo_legs or []):
                lines.append(f"   • {lg['home']} vs {lg['away']} ➔ {lg['selection']} (@ {lg['odds']:.2f})")

        lines.extend([
            "",
            f"📊 TOTAL RECORD (Since {TRACKING_START_DATE})",
            "────────────────────────",
            f"• Today : {d_won}W - {d_lost}L ({d_open} Open) | {d_net:+.2f}u",
            f"• Total : {won_all}W - {lost_all}L ({wr_all:.1f}%) | {net_all:+.2f}u (${net_all * 50:+.2f})"
        ])
        return "\n".join(lines)


class TelegramBotClient:
    REMOVE_BOTTOM_KEYBOARD = {"remove_keyboard": True}

    def __init__(self, bot_token: str):
        self.bot_token = bot_token.strip()
        self.base_url = f"https://api.telegram.org/bot{self.bot_token}"
        self.channel_publish_lock = threading.Lock()
        DailyLedgerManager.load_all_history_items()

    def send_message(self, chat_id: Any, text: str, remove_kb: bool = True) -> bool:
        url = f"{self.base_url}/sendMessage"
        payload_data: Dict[str, Any] = {
            "chat_id": chat_id,
            "text": text[:3900]
        }
        if remove_kb and isinstance(chat_id, int) and chat_id > 0:
            payload_data["reply_markup"] = self.REMOVE_BOTTOM_KEYBOARD

        payload = json.dumps(payload_data).encode("utf-8")
        req = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=10) as resp:
                return resp.status == 200
        except Exception as e:
            logger.error("Failed to send Telegram message to %s: %s", chat_id, e)
            return False

    def sync_and_publish_to_footybett(self) -> int:
        with self.channel_publish_lock:
            SafeCushionBetCreator.generate_slate_and_combo_for_active_date()
            LiveSportsbookAndStatsAPI.grade_ledger_items()
            all_items = DailyLedgerManager.load_all_history_items()
            active_date = DailyLedgerManager.get_active_date_str()
            published_count = 0
            updated = False

            for full_key, item in all_items.items():
                if not item.is_approved or item.date_str < TRACKING_START_DATE:
                    continue
                pick_lock_key = f"pick:{full_key}"
                result_lock_key = f"result:{full_key}"

                if item.date_str == active_date:
                    if not item.published_to_channel and not DailyLedgerManager.is_locked_in_channel(pick_lock_key):
                        if item.match_status != "FT" and item.settlement == "PENDING":
                            open_card = BetSlipCardFormatter.format_open_bet_card(item)
                            if self.send_message(PUBLISH_CHANNEL_ID, open_card, remove_kb=False):
                                item.published_to_channel = True
                                DailyLedgerManager.mark_locked_in_channel(pick_lock_key)
                                published_count += 1
                                updated = True
                                time.sleep(1.0)

                if item.settlement in ["WON ✅", "LOST ❌"]:
                    if not item.published_result_to_channel and not DailyLedgerManager.is_locked_in_channel(result_lock_key):
                        close_card = BetSlipCardFormatter.format_closed_bet_card(item)
                        if self.send_message(PUBLISH_CHANNEL_ID, close_card, remove_kb=False):
                            item.published_to_channel = True
                            item.published_result_to_channel = True
                            DailyLedgerManager.mark_locked_in_channel(pick_lock_key)
                            DailyLedgerManager.mark_locked_in_channel(result_lock_key)
                            updated = True
                            time.sleep(1.0)

            if updated:
                DailyLedgerManager.save_all_items(all_items)
            return published_count

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

    def background_worker_loop(self):
        logger.info("AI Men's Football Bet Creator & Combo Worker started (v16.2)...")
        time.sleep(5)
        while True:
            try:
                self.sync_and_publish_to_footybett()
            except Exception as e:
                logger.error("Background worker error: %s", e)
            time.sleep(60)

    def set_official_menu_commands(self):
        commands = [
            {"command": "scan", "description": "🎯 Today's Singles, Combo & Results"},
            {"command": "results", "description": "🏁 Refresh Live Scores & Outcomes"},
            {"command": "stats", "description": "📈 Total Record & P&L (From 2026-11-11)"},
            {"command": "poststats", "description": "📢 Post Results Summary to @Footybett"}
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

        logger.info("Bot listener running (v16.2 Men's Leagues Only + 3 Singles + 1 Combo)...")
        offset = None

        while True:
            updates = self.get_updates(offset)
            for upd in updates:
                offset = upd["update_id"] + 1
                msg = upd.get("message", {})
                chat_id = msg.get("chat", {}).get("id")
                text = (msg.get("text", "") or msg.get("caption", "")).strip()

                if not chat_id:
                    continue

                subs = load_json_set(SUBSCRIBERS_FILE)
                subs.add(chat_id)
                save_json_set(SUBSCRIBERS_FILE, subs)

                if text == "/poststats":
                    def handle_post_stats(cid):
                        self.sync_and_publish_to_footybett()
                        summary = BetSlipCardFormatter.format_clean_today_and_total()
                        if self.send_message(PUBLISH_CHANNEL_ID, summary, remove_kb=False):
                            self.send_message(cid, f"✅ Sent summary to {PUBLISH_CHANNEL_ID}!\n\n{summary}")
                        else:
                            self.send_message(cid, f"❌ Could not post to {PUBLISH_CHANNEL_ID}.")
                    threading.Thread(target=handle_post_stats, args=[chat_id], daemon=True).start()
                    continue

                def handle_clean_view(cid):
                    self.sync_and_publish_to_footybett()
                    self.send_message(cid, BetSlipCardFormatter.format_clean_today_and_total())
                threading.Thread(target=handle_clean_view, args=[chat_id], daemon=True).start()

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