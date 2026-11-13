"""
Telegram Pro Football Betting Syndicate — Deep Match-Autopsy Self-Learning Engine
& Automatic End-of-Day Channel Recap Publisher (v18.3 Final Production Release)
(@betyyyybot -> @Footybett)

What's New in v18.3 (True Match-Stats Autopsy & Root-Cause Learning):
1. Deep Post-Match Boxscore Autopsy (`LiveSportsbookAndStatsAPI.fetch_match_autopsy_stats`):
   - Whenever a bet settles as LOST ❌, the bot queries ESPN's full Match Summary API (`/summary?event=<id>`)
     to inspect WHAT ACTUALLY HAPPENED on the pitch:
     • Possession % (`home_poss` vs `away_poss`)
     • Total Shots & Shots on Target (`shots (sot)`)
     • Red Cards (`red_cards`) & Yellow Cards
     • Corner Kicks (`corners`)
     • Halftime vs Second-Half Goal Timing (`key_events`)
2. Root-Cause Diagnosis (`diagnose_loss_root_cause`) & Rule Updates:
   -Instead of only looking at the final score, the bot classifies the exact reason its prediction failed:
     • `RED_CARD_ANOMALY`: A team got a Red Card that broke the tactical projection -> Marks the loss as a
       discipline anomaly so a good strategy isn't falsely punished, while flagging high-card risk.
     • `FINISHING_VARIANCE_HIGH_SHOTS`: Teams generated 14+ shots / 6+ on target (model pace was right,
       goalkeepers made 6+ saves) -> Records high shot volume & prefers `Over 1.5` / `BTTS` cushion.
     • `TACTICAL_LOW_PACE_TRAP`: Match had < 18 total shots or < 5 shots on target (dead midfield game) ->
       Flags the league/teams in `low_goal_trap_leagues` and raises the required attacking threshold.
     • `STERILE_POSSESSION_DRAW_TRAP`: Favorite had 60%+ possession and 12+ shots but couldn't break a
       parked bus (`1-1` or `0-0`) -> Switches future favorites in that league to `Draw No Bet (DNB)`.
     • `DEFENSIVE_COLLAPSE_UPSET`: Favorite conceded 2+ goals on counter-attacks despite pre-match form ->
       Flags team/league defensive vulnerability and blocks raw `1x2` picks on that team.
3. Full Root-Cause Autopsy Printed on Closed Loss Cards & `/learn`:
   - Every settled loss card on `@Footybett` and `/learn` in `@betyyyybot` shows the exact match stats
     (Shots, On Target, Possession, Red Cards) and the exact rule adjustment made for tomorrow!
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
LEARNING_WEIGHTS_FILE = os.path.join(BASE_DIR, "learning_weights.json")

API_FOOTBALL_KEY = os.environ.get("API_FOOTBALL_KEY", "")
PUBLISH_CHANNEL_ID = os.environ.get("PUBLISH_CHANNEL_ID", "@Footybett")

TRACKING_START_DATE = "2026-11-11"
MIN_SINGLE_ODDS = 1.52
MAX_DAILY_SINGLES = 3

MIN_HOURS_BEFORE_KICKOFF = 0.25
IDEAL_MAX_HOURS_BEFORE_KICKOFF = 4.0
ADAPTIVE_MAX_HOURS_BEFORE_KICKOFF = 5.5

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

BCGAME_VERIFIED_MENS_LEAGUES: List[Tuple[str, str]] = [
    ("uefa.champions", "UEFA Champions League"),
    ("uefa.europa", "UEFA Europa League"),
    ("uefa.europa.conf", "UEFA Conference League"),
    ("uefa.nations", "UEFA Nations League"),
    ("fifa.worldq.uefa", "WC Qualifiers - Europe"),
    ("fifa.worldq.conmebol", "WC Qualifiers - South America"),
    ("fifa.worldq.concacaf", "WC Qualifiers - CONCACAF"),
    ("fifa.worldq.caf", "WC Qualifiers - Africa"),
    ("fifa.worldq.afc", "WC Qualifiers - Asia"),
    ("eng.1", "England - Premier League"),
    ("esp.1", "Spain - LaLiga"),
    ("ita.1", "Italy - Serie A"),
    ("ger.1", "Germany - Bundesliga"),
    ("fra.1", "France - Ligue 1"),
    ("ned.1", "Netherlands - Eredivisie"),
    ("por.1", "Portugal - Liga Portugal"),
    ("bra.1", "Brazil - Brasileirão Série A"),
    ("arg.1", "Argentina - Liga Profesional"),
    ("eng.2", "England - Championship"),
    ("esp.2", "Spain - LaLiga 2"),
    ("ita.2", "Italy - Serie B"),
    ("ger.2", "Germany - 2. Bundesliga"),
    ("fra.2", "France - Ligue 2"),
    ("tur.1", "Turkey - Süper Lig"),
    ("bel.1", "Belgium - Pro League"),
    ("sco.1", "Scotland - Premiership"),
    ("usa.1", "USA - MLS"),
    ("mex.1", "Mexico - Liga MX"),
    ("col.1", "Colombia - Primera A"),
    ("chi.1", "Chile - Primera División"),
    ("bra.2", "Brazil - Série B"),
    ("eng.3", "England - League One"),
]

LOW_SCORING_TACTICAL_LEAGUE_SLUGS = {
    "bra.2", "arg.1", "ita.2", "esp.2", "fra.2", "col.1", "fifa.worldq.conmebol", "fifa.worldq.caf"
}

BANNED_RAW_JSON_TERMS = [
    "-women", "women's", "womens", "femenil", "femenina", "feminin", "frauen", "ladies",
    "wchampions", "weuro", "wworld", "nwsl", "eng.w.", "esp.w.", "ita.w.", "ger.w.", "fra.w.", "usa.w.", "mex.w.",
    "efl trophy", "papa johns", "vertu trophy", "u21", "u23", "u19", "u18", "u20", "u17",
    "youth", "reserve", "simulated", "srl", "cyber", "esports",
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
    "turkiye": "turkey",
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


def parse_kickoff_utc(raw_date_str: str) -> Optional[datetime.datetime]:
    if not raw_date_str:
        return None
    try:
        clean = raw_date_str.replace("Z", "+00:00")
        dt = datetime.datetime.fromisoformat(clean)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=datetime.timezone.utc)
        return dt.astimezone(datetime.timezone.utc)
    except Exception:
        return None


def format_kickoff_human(dt: Optional[datetime.datetime]) -> str:
    if not dt:
        return ""
    now = datetime.datetime.now(datetime.timezone.utc)
    diff_min = int((dt - now).total_seconds() / 60.0)
    leb_dt = dt + datetime.timedelta(hours=2)
    time_str = f"{leb_dt.strftime('%H:%M')} Local ({dt.strftime('%H:%M UTC')})"
    if diff_min <= 0:
        return f"{time_str} — Starting Soon"
    h = diff_min // 60
    m = diff_min % 60
    rel_str = f"In {h}h {m}m" if h > 0 else f"In {m}m"
    return f"{time_str} ({rel_str})"


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
    market_type: str  # "1x2", "dnb", "btts", "goals_over_under", "daily_parlay"
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
    bookmaker_name: str = "BC.Game"
    kickoff_str: str = ""
    alt_bcgame_line: str = ""
    loss_autopsy: str = ""
    failure_mode: str = ""
    is_combo: bool = False
    combo_legs: Optional[List[Dict[str, Any]]] = None
    match_status: str = "PENDING"
    score_str: str = "-"
    settlement: str = "PENDING"  # PENDING, WON ✅, LOST ❌, PUSH ➖
    notified_settled: bool = False
    published_to_channel: bool = False
    published_result_to_channel: bool = False


class DailyLedgerManager:
    """Manages Active Slate, Historical Ledger (since 2026-11-11), and Permanent Channel Locks."""

    @classmethod
    def get_active_date_str(cls) -> str:
        now_utc = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
        return max(now_utc, TRACKING_START_DATE)

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
    def load_all_history_items(cls) -> Dict[str, LedgerBetItem]:
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
    def load_yesterday_items(cls) -> List[LedgerBetItem]:
        all_items = cls.load_all_history_items()
        y_str = cls.get_yesterday_str()
        return [v for v in all_items.values() if v.date_str == y_str and v.is_approved]

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


class SelfLearningEngine:
    """
    Deep Match-Autopsy & Root-Cause Self-Learning Engine (v18.3):
    1. Inspects actual post-match boxscore stats (Shots, Shots on Target, Possession %, Red Cards, Corners)
       fetched via `LiveSportsbookAndStatsAPI.fetch_match_autopsy_stats(event_id)` whenever a pick loses.
    2. Diagnoses WHY the prediction failed (`diagnose_loss_root_cause`) across 5 distinct root causes:
       - `RED_CARD_ANOMALY`: Red card ruined the tactical script -> Does NOT penalize the core strategy weight,
         logs discipline variance.
       - `FINISHING_VARIANCE_HIGH_SHOTS`: Teams had 14+ shots & 6+ on target (pace projection was right, keepers
         made 6+ saves or hit woodwork) -> Routes future balanced games in that league to `BTTS: Yes` / `Over 1.5`.
       - `TACTICAL_LOW_PACE_TRAP`: Match had < 16 total shots or < 5 on target (slow midfield block) ->
         Flags league/teams in `low_goal_trap_leagues` and raises required attacking threshold.
       - `STERILE_POSSESSION_DRAW_TRAP`: Favorite had 58%+ possession / more shots but drew (`1-1`, `0-0`) ->
         Flags league in `draw_trap_leagues` and auto-switches future favorites to `Draw No Bet (DNB)`.
       - `DEFENSIVE_COLLAPSE_UPSET`: Favorite conceded 2+ goals on counter-attacks -> Flags team in
         `unreliable_favorites` and blocks raw `1x2` picks on that team.
    """

    @staticmethod
    def classify_strategy_key(item: LedgerBetItem) -> str:
        if item.is_combo:
            return "daily_combo"
        if item.market_type == "btts":
            return "btts_yes"
        if item.market_type == "dnb":
            return "draw_no_bet"
        if item.market_type == "goals_over_under":
            return "under_25" if "under" in item.selection.lower() else "over_25"
        return "1x2_winner"

    @classmethod
    def diagnose_loss_root_cause(
        cls,
        item: LedgerBetItem,
        gh: int,
        ga: int,
        stats: Dict[str, Any]
    ) -> Tuple[str, str]:
        """
        Returns `(failure_mode_code, human_readable_autopsy_and_fix)` using real post-match boxscore stats!
        """
        s_key = cls.classify_strategy_key(item)
        tot_g = gh + ga
        h_shots = stats.get("h_shots", 0)
        a_shots = stats.get("a_shots", 0)
        tot_shots = h_shots + a_shots
        h_sot = stats.get("h_sot", 0)
        a_sot = stats.get("a_sot", 0)
        tot_sot = h_sot + a_sot
        h_poss = stats.get("h_poss", 50)
        a_poss = stats.get("a_poss", 50)
        h_red = stats.get("h_red", 0)
        a_red = stats.get("a_red", 0)
        tot_red = h_red + a_red

        has_boxscore = tot_shots > 0
        stats_tag = (
            f"[Stats: {h_shots}+{a_shots}={tot_shots} Shots ({tot_sot} On Target) | Poss: {h_poss}%-{a_poss}%]"
            if has_boxscore
            else f"[Final: {gh}-{ga}]"
        )

        # 1. Red Card / Discipline Anomaly
        if tot_red > 0:
            red_team = item.team_home if h_red > 0 else item.team_away
            return (
                "RED_CARD_ANOMALY",
                f"🔍 Why It Lost: Red card to {red_team} ({tot_red} RC) broke the tactical game script {stats_tag} ➔ Fix: Logged as red-card anomaly (strategy weight protected)."
            )

        # 2. Over 2.5 Loss Diagnosis
        if s_key == "over_25":
            if gh == 1 and ga == 1:
                if has_boxscore and tot_shots >= 22:
                    return (
                        "FINISHING_VARIANCE_1_1_DRAW",
                        f"🔍 Why It Lost: High-tempo 1-1 draw ({tot_shots} shots, {tot_sot} on target — keepers denied 3rd goal) ➔ Fix: Auto-pivoting balanced {item.match_context} games to BTTS: Yes (cashes on 1-1!)."
                    )
                return (
                    "TACTICAL_1_1_STALEMATE",
                    f"🔍 Why It Lost: Teams settled for a 1-1 draw after trading goals {stats_tag} ➔ Fix: Auto-pivoting balanced {item.match_context} games to BTTS: Yes (cashes on 1-1!)."
                )
            if has_boxscore and (tot_shots >= 24 or tot_sot >= 8):
                return (
                    "FINISHING_VARIANCE_HIGH_SHOTS",
                    f"🔍 Why It Lost: Extreme goalkeeper/finishing variance — {tot_shots} shots & {tot_sot} on target only produced {tot_g} goal(s) ➔ Fix: Requiring higher conversion form in {item.match_context}."
                )
            return (
                "TACTICAL_LOW_PACE_TRAP",
                f"🔍 Why It Lost: Low-tempo midfield block ({tot_g} goals, only {tot_sot} shots on target) {stats_tag} ➔ Fix: Flagged {item.match_context} as low-pace; raised Over/BTTS form requirement."
            )

        # 3. BTTS: Yes Loss Diagnosis
        if s_key == "btts_yes":
            zero_team = item.team_home if gh == 0 else item.team_away
            if has_boxscore and tot_sot >= 7:
                return (
                    "FINISHING_VARIANCE_BTTS",
                    f"🔍 Why It Lost: {zero_team} failed to convert despite {tot_shots} match shots ({tot_sot} on target) ➔ Fix: Raising away/home scoring floor in {item.match_context}."
                )
            return (
                "ONE_SIDED_SHUTOUT_TRAP",
                f"🔍 Why It Lost: {zero_team} was shut out ({gh}-{ga}) with low attacking threat {stats_tag} ➔ Fix: Requiring stricter scoring streak in {item.match_context}."
            )

        # 4. 1x2 Winner or DNB Loss Diagnosis
        if s_key in ["1x2_winner", "draw_no_bet"]:
            if gh == ga:
                return (
                    "STERILE_POSSESSION_DRAW_TRAP",
                    f"🔍 Why It Lost: Favorite held to a {gh}-{ga} draw despite {max(h_poss, a_poss)}% possession {stats_tag} ➔ Fix: Auto-switching {item.match_context} favorites from 1x2 to Draw No Bet (DNB)."
                )
            return (
                "DEFENSIVE_COLLAPSE_UPSET",
                f"🔍 Why It Lost: Defensive breakdown — conceded {max(gh, ga)} counter-attack goals in {gh}-{ga} upset {stats_tag} ➔ Fix: Blocked raw 1x2 favorite bets on {item.team_home}/{item.team_away}."
            )

        # 5. Under 2.5 Loss Diagnosis
        if s_key == "under_25":
            return (
                "HIGH_TEMPO_SHOOTOUT_TRAP",
                f"🔍 Why It Lost: Open {gh}-{ga} shootout ({tot_g} goals from {tot_sot} shots on target) broke Under 2.5 {stats_tag} ➔ Fix: Blocked Under 2.5 in {item.match_context}."
            )

        return (
            "COMBO_LEG_VARIANCE",
            f"🔍 Why It Lost: One combo leg missed ({item.score_str}) ➔ Fix: Tightened combo leg safety cushion."
        )

    @classmethod
    def recalibrate_from_ledger(cls) -> Dict[str, Any]:
        all_items = list(DailyLedgerManager.load_all_history_items().values())
        settled = [i for i in all_items if i.is_approved and i.settlement in ["WON ✅", "LOST ❌"]]

        strat_stats: Dict[str, Dict[str, Any]] = {}
        league_stats: Dict[str, Dict[str, Any]] = {}
        draw_trap_leagues: Set[str] = set()
        btts_preferred_leagues: Set[str] = set()
        low_goal_trap_leagues: Set[str] = set()
        high_shootout_trap_leagues: Set[str] = set()
        unreliable_teams: Set[str] = set()
        lessons_learned: List[str] = []

        for item in settled:
            s_key = cls.classify_strategy_key(item)
            lg_key = item.match_context or "General"
            is_win = "WON" in item.settlement

            st = strat_stats.setdefault(s_key, {"won": 0, "lost": 0, "net_u": 0.0, "ev_mod": 0.0, "status": "ACTIVE"})
            lg = league_stats.setdefault(lg_key, {"won": 0, "lost": 0, "net_u": 0.0, "ev_mod": 0.0})

            if is_win:
                prof = item.recommended_units * (item.odds - 1.0)
                st["won"] += 1
                st["net_u"] = round(st["net_u"] + prof, 2)
                lg["won"] += 1
                lg["net_u"] = round(lg["net_u"] + prof, 2)
            else:
                st["lost"] += 1
                st["net_u"] = round(st["net_u"] - item.recommended_units, 2)
                lg["lost"] += 1
                lg["net_u"] = round(lg["net_u"] - item.recommended_units, 2)

                f_mode = item.failure_mode or ""
                m_sc = re.search(r"(\d+)\s*-\s*(\d+)", item.score_str or "")
                gh, ga = (int(m_sc.group(1)), int(m_sc.group(2))) if m_sc else (0, 0)
                tot_g = gh + ga

                if "1_1" in f_mode or (s_key == "over_25" and gh == 1 and ga == 1):
                    btts_preferred_leagues.add(lg_key)
                if "DRAW_TRAP" in f_mode or (s_key == "1x2_winner" and gh == ga):
                    draw_trap_leagues.add(lg_key)
                if "LOW_PACE" in f_mode or "SHUTOUT" in f_mode or (s_key in ["over_25", "btts_yes"] and tot_g <= 1):
                    low_goal_trap_leagues.add(lg_key)
                if "SHOOTOUT" in f_mode or (s_key == "under_25" and tot_g >= 3):
                    high_shootout_trap_leagues.add(lg_key)
                if "DEFENSIVE_COLLAPSE" in f_mode:
                    unreliable_teams.add(normalize_team_str(item.team_home))

                if item.loss_autopsy:
                    lessons_learned.append(f"{item.team_home} vs {item.team_away} ({item.score_str}): {item.loss_autopsy}")
                elif s_key == "over_25" and gh == 1 and ga == 1:
                    lessons_learned.append(
                        f"{item.team_home} 1-1 {item.team_away}: 1-1 Draw on Over 2.5 ➔ Auto-pivoting balanced {lg_key} games to BTTS: Yes."
                    )

        for s_key, d in strat_stats.items():
            w, l = d["won"], d["lost"]
            tot = w + l
            wr = (w / tot * 100.0) if tot > 0 else 0.0
            d["win_rate"] = round(wr, 1)
            net_diff = w - l
            if net_diff > 0:
                d["ev_mod"] = min(6.0, round(net_diff * 2.5, 1))
                d["status"] = "🔥 HOT (Boosted)"
            elif net_diff < 0:
                d["ev_mod"] = max(-12.0, round(net_diff * 4.5, 1))
                d["status"] = "❄️ COOLDOWN (Tightened)" if (tot >= 2 and wr <= 35.0) else "⚠️ CAUTIOUS"
            else:
                d["ev_mod"] = 0.0
                d["status"] = "⚖️ NEUTRAL"

        for lg_key, d in league_stats.items():
            net_diff = d["won"] - d["lost"]
            d["ev_mod"] = max(-8.0, min(5.0, round(net_diff * 3.0, 1)))

        state = {
            "updated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "strategies": strat_stats,
            "leagues": league_stats,
            "draw_trap_leagues": sorted(draw_trap_leagues),
            "btts_preferred_leagues": sorted(btts_preferred_leagues),
            "low_goal_trap_leagues": sorted(low_goal_trap_leagues),
            "high_shootout_trap_leagues": sorted(high_shootout_trap_leagues),
            "unreliable_teams": sorted(unreliable_teams),
            "lessons_learned": lessons_learned[-8:]
        }
        save_json_dict(LEARNING_WEIGHTS_FILE, state)
        return state

    @classmethod
    def get_learning_state(cls) -> Dict[str, Any]:
        return cls.recalibrate_from_ledger()

    @classmethod
    def format_learning_report(cls) -> str:
        st = cls.recalibrate_from_ledger()
        strats = st.get("strategies", {})
        lessons = st.get("lessons_learned", [])

        lines = [
            "🧠 DEEP MATCH-AUTOPSY & SELF-LEARNING ENGINE (v18.3)",
            "────────────────────────"
        ]
        if strats:
            lines.append("📊 MARKET PERFORMANCE & AUTO-WEIGHTS:")
            for k, v in sorted(strats.items(), key=lambda kv: kv[1].get("net_u", 0.0), reverse=True):
                lines.append(
                    f"• {k}: {v['won']}W-{v['lost']}L ({v['win_rate']}%) | {v['net_u']:+.2f}u | EV Adj: {v['ev_mod']:+.1f}% [{v['status']}]"
                )
        else:
            lines.append("• Calibrating baseline weights (waiting for settled matches).")

        lines.append("")
        lines.append("🔬 POST-MATCH AUTOPSY & LEARNED RULES:")
        if lessons:
            for ls in lessons:
                lines.append(f"• {ls}")
        else:
            lines.append("• Active Guardrails: Post-match Shots/Possession/Red-Card autopsy active on every settled pick.")

        return "\n".join(lines)


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
                with urllib.request.urlopen(req, timeout=5) as resp:
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
    def fetch_match_autopsy_stats(cls, event_id: str, swapped: bool = False) -> Dict[str, Any]:
        """
        Fetches full post-match boxscore statistics (Shots, Shots on Target, Possession %, Red Cards, Corners)
        from ESPN's `/summary?event=<id>` endpoint so the bot knows WHY a match won or lost!
        """
        stats = {
            "h_shots": 0, "a_shots": 0,
            "h_sot": 0, "a_sot": 0,
            "h_poss": 50, "a_poss": 50,
            "h_red": 0, "a_red": 0,
            "h_corners": 0, "a_corners": 0
        }
        if not event_id:
            return stats
        url = f"{cls.ESPN_SUMMARY_URL}?event={event_id}"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                teams = data.get("boxscore", {}).get("teams", [])
                if len(teams) >= 2:
                    t_home = teams[1] if swapped else teams[0]
                    t_away = teams[0] if swapped else teams[1]
                    for prefix, t_obj in [("h", t_home), ("a", t_away)]:
                        for st in t_obj.get("statistics", []):
                            nm = (st.get("name") or "").lower()
                            val_str = str(st.get("displayValue", "0")).replace("%", "").strip()
                            try:
                                val = int(float(val_str))
                            except Exception:
                                continue
                            if nm in ["totalshots", "shots"]:
                                stats[f"{prefix}_shots"] = val
                            elif nm in ["shotsontarget", "shotsongoal"]:
                                stats[f"{prefix}_sot"] = val
                            elif "possession" in nm:
                                stats[f"{prefix}_poss"] = val
                            elif "redcard" in nm:
                                stats[f"{prefix}_red"] = val
                            elif "corner" in nm:
                                stats[f"{prefix}_corners"] = val
        except Exception:
            pass
        return stats

    @classmethod
    def _parse_espn_event(
        cls,
        ev: Dict[str, Any],
        default_league_title: str,
        default_slug: str,
        rank_idx: int,
        now_utc: datetime.datetime
    ) -> Optional[Dict[str, Any]]:
        raw_ev_dump = json.dumps(ev).lower()
        if any(b in raw_ev_dump for b in BANNED_RAW_JSON_TERMS):
            return None

        ev_id = str(ev.get("id", ""))
        comps = ev.get("competitions", [])
        if not comps:
            return None
        comp = comps[0]
        competitors = comp.get("competitors", [])
        if len(competitors) < 2:
            return None

        home_c = next((c for c in competitors if c.get("homeAway") == "home"), competitors[0])
        away_c = next((c for c in competitors if c.get("homeAway") == "away"), competitors[1])

        h_name = home_c.get("team", {}).get("displayName") or home_c.get("team", {}).get("name", "")
        a_name = away_c.get("team", {}).get("displayName") or away_c.get("team", {}).get("name", "")
        if not h_name or not a_name:
            return None

        raw_date = comp.get("date") or ev.get("date") or ""
        kickoff_dt = parse_kickoff_utc(raw_date)
        hours_left = None
        if kickoff_dt:
            hours_left = (kickoff_dt - now_utc).total_seconds() / 3600.0

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

        home_ml_dec, away_ml_dec, draw_ml_dec, ou_line, over_dec, under_dec = None, None, None, None, None, None
        has_live_odds = False
        odds_list = comp.get("odds", [])
        if odds_list and isinstance(odds_list[0], dict):
            od = odds_list[0]
            ou_line = od.get("overUnder")
            over_dec = cls._american_to_decimal(od.get("overOdds"))
            under_dec = cls._american_to_decimal(od.get("underOdds"))
            h_ml = od.get("homeTeamOdds", {}).get("moneyLine")
            a_ml = od.get("awayTeamOdds", {}).get("moneyLine")
            d_ml = od.get("drawOdds", {}).get("moneyLine")
            home_ml_dec = cls._american_to_decimal(h_ml)
            away_ml_dec = cls._american_to_decimal(a_ml)
            draw_ml_dec = cls._american_to_decimal(d_ml)
            if home_ml_dec or away_ml_dec or over_dec:
                has_live_odds = True

        return {
            "event_id": ev_id,
            "apif_fixture_id": "",
            "priority_rank": rank_idx + (0 if has_live_odds else 15),
            "has_live_odds": has_live_odds,
            "home": h_name,
            "away": a_name,
            "kickoff_dt": kickoff_dt,
            "kickoff_str": format_kickoff_human(kickoff_dt),
            "hours_until_kickoff": hours_left,
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
            "league_name": default_league_title,
            "league_slug": default_slug,
            "bookmaker": "BC.Game",
            "home_odds": home_ml_dec,
            "away_odds": away_ml_dec,
            "draw_odds": draw_ml_dec,
            "ou_line": ou_line,
            "over_odds": over_dec,
            "under_odds": under_dec,
        }

    @classmethod
    def fetch_mens_fixtures_with_odds(cls, date_str: str) -> List[Dict[str, Any]]:
        espn_date = date_str.replace("-", "")
        results: List[Dict[str, Any]] = []
        seen_match_keys: Set[str] = set()
        now_utc = datetime.datetime.now(datetime.timezone.utc)

        for rank_idx, (slug, league_title) in enumerate(BCGAME_VERIFIED_MENS_LEAGUES):
            url = f"{cls.ESPN_LEAGUE_SCOREBOARD_TEMPLATE.format(slug=slug)}?dates={espn_date}&limit=100"
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            try:
                with urllib.request.urlopen(req, timeout=4) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                    for ev in data.get("events", []):
                        parsed = cls._parse_espn_event(ev, league_title, slug, rank_idx, now_utc)
                        if not parsed:
                            continue
                        m_key = f"{normalize_team_str(parsed['home'])}_vs_{normalize_team_str(parsed['away'])}"
                        if m_key not in seen_match_keys:
                            seen_match_keys.add(m_key)
                            results.append(parsed)
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

        if market_type == "dnb" and is_finished:
            sel_low = selection.lower()
            for_away = teams_match(team_away, sel_low) and not teams_match(team_home, sel_low)
            if gh == ga:
                return "PUSH ➖"
            if for_away:
                return "WON ✅" if ga > gh else "LOST ❌"
            return "WON ✅" if gh > ga else "LOST ❌"

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
            if item.settlement == "PENDING" or (item.settlement == "LOST ❌" and not item.loss_autopsy):
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
                    leg_res = cls.grade_single_condition(
                        leg.get("market_type", "goals_over_under"),
                        leg.get("selection", ""),
                        leg.get("line"),
                        gh,
                        ga,
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
                elif leg_statuses and all("WON" in st or "PUSH" in st for st in leg_statuses):
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

                item.score_str = f"{gh}-{ga} ({status_label})"
                item.match_status = "FT" if is_finished else ("LIVE" if is_live else status_label)

                item.settlement = cls.grade_single_condition(
                    item.market_type,
                    item.selection,
                    item.line,
                    gh,
                    ga,
                    is_finished,
                    item.team_home,
                    item.team_away
                )

                # If settled as LOST ❌, run the Deep Match-Autopsy to learn WHY it lost!
                if item.settlement == "LOST ❌" and not item.loss_autopsy:
                    box_stats = cls.fetch_match_autopsy_stats(matched.get("event_id", ""), swapped=swapped)
                    f_mode, autopsy_str = SelfLearningEngine.diagnose_loss_root_cause(item, gh, ga, box_stats)
                    item.failure_mode = f_mode
                    item.loss_autopsy = autopsy_str

            if item.settlement in ["WON ✅", "LOST ❌"] and not item.notified_settled:
                item.notified_settled = True
                newly_settled.append(item)

        DailyLedgerManager.save_all_items(all_items)
        SelfLearningEngine.recalibrate_from_ledger()
        return newly_settled


class SafeCushionBetCreator:
    """
    Self-Learning BC.Game Market Selector (v18.3):
    Applies all learned rules from `SelfLearningEngine` (`btts_preferred_leagues`, `draw_trap_leagues`,
    `low_goal_trap_leagues`, `high_shootout_trap_leagues`, and `unreliable_teams`).
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
        buzz_teams: Set[str],
        learning_state: Dict[str, Any],
        max_hours_ahead: float = IDEAL_MAX_HOURS_BEFORE_KICKOFF
    ) -> Tuple[Optional[LedgerBetItem], Optional[Dict[str, Any]]]:
        if m["is_finished"] or m["is_live"]:
            return None, None
        hours_left = m.get("hours_until_kickoff")
        if hours_left is None:
            return None, None
        if hours_left < MIN_HOURS_BEFORE_KICKOFF or hours_left > max_hours_ahead:
            return None, None

        home = m["home"]
        away = m["away"]
        slug = m.get("league_slug", "")
        kickoff_str = m.get("kickoff_str", "")
        h_form = m.get("home_form", "")[-5:]
        a_form = m.get("away_form", "")[-5:]
        hw, hd, hl = cls._parse_w_d_l(m.get("home_record", ""), h_form)
        aw, ad, al = cls._parse_w_d_l(m.get("away_record", ""), a_form)

        h_games = max(1, hw + hd + hl)
        a_games = max(1, aw + ad + al)
        h_win_rate = hw / h_games if (hw + hd + hl) > 0 else 0.45
        a_win_rate = aw / a_games if (aw + ad + al) > 0 else 0.35

        h_recent_w = h_form.count("W") if h_form else int(round(h_win_rate * 5))
        h_recent_d = h_form.count("D") if h_form else 1
        h_recent_l = h_form.count("L") if h_form else int(round((hl / h_games) * 5))
        a_recent_w = a_form.count("W") if a_form else int(round(a_win_rate * 5))
        a_recent_d = a_form.count("D") if a_form else 1
        a_recent_l = a_form.count("L") if a_form else int(round((al / a_games) * 5))
        combined_draws = h_recent_d + a_recent_d

        has_channel_buzz = (normalize_team_str(home) in buzz_teams) or (normalize_team_str(away) in buzz_teams)
        buzz_tag = " + Syndicate Radar" if has_channel_buzz else ""
        bookie = "BC.Game"
        league_label = m.get("league_name") or "Men's Pro League"

        live_over_odds = m.get("over_odds")
        live_under_odds = m.get("under_odds")
        live_home_odds = m.get("home_odds")
        live_away_odds = m.get("away_odds")

        strats_mem = learning_state.get("strategies", {})
        leagues_mem = learning_state.get("leagues", {})
        draw_traps = set(learning_state.get("draw_trap_leagues", []))
        btts_pref = set(learning_state.get("btts_preferred_leagues", []))
        low_goal_traps = set(learning_state.get("low_goal_trap_leagues", []))
        shootout_traps = set(learning_state.get("high_shootout_trap_leagues", []))
        unreliable_teams = set(learning_state.get("unreliable_teams", []))

        lg_mod = leagues_mem.get(league_label, {}).get("ev_mod", 0.0)
        base_boost = (4.0 if has_channel_buzz else 0.0) + lg_mod

        def strat_mod(s_key: str) -> float:
            return strats_mem.get(s_key, {}).get("ev_mod", 0.0)

        def is_in_cooldown(s_key: str) -> bool:
            return "COOLDOWN" in strats_mem.get(s_key, {}).get("status", "")

        # Strategy 1: Strong Home Favorite -> BC.Game `1x2: {Home} to Win` (or Auto-DNB if Draw Trap league or unreliable team)
        if (h_recent_w >= 3 and h_recent_l <= 1 and h_win_rate >= a_win_rate + 0.14) or (
            live_home_odds and 1.52 <= live_home_odds <= 1.85
        ):
            if league_label in draw_traps or normalize_team_str(home) in unreliable_teams or is_in_cooldown("1x2_winner"):
                selection = f"Draw No Bet ➔ {home}"
                alt_line = f"Double Chance ➔ {home} or Draw (1X)"
                market_type = "dnb"
                odds = 1.56
                ev_val = 15.0 + base_boost + strat_mod("draw_no_bet")
                why = f"{home} strong home form ({h_form or 'Favored'}); auto-protected with Draw No Bet{buzz_tag}."
            else:
                odds = live_home_odds if (live_home_odds and 1.52 <= live_home_odds <= 1.95) else 1.62
                selection = f"1x2 ➔ {home} to Win"
                alt_line = f"Draw No Bet ➔ {home} (or Total ➔ Over 1.5 Goals)"
                market_type = "1x2"
                ev_val = 15.0 + base_boost + strat_mod("1x2_winner")
                why = f"{home} dominant home form ({h_form or m.get('home_record') or 'Favored'}) vs {away}{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "1x2",
                "selection": f"Double Chance: {home} or Draw (1X)", "line": None, "odds": 1.28
            }
            single = cls._build_single(date_str, home, away, market_type, selection, None, odds, 71.0, ev_val, why, league_label, bookie, kickoff_str, alt_line)
            return single, combo_leg

        # Strategy 2: Active Scoring OR Draw-Prone Attacking Match (Armenia 1-1 Cyprus Rule) -> `Both Teams to Score ➔ Yes`
        min_w_for_btts = 2 if league_label not in low_goal_traps else 3
        if (
            ((h_recent_w >= min_w_for_btts and a_recent_w >= min_w_for_btts) or (h_recent_w + a_recent_w >= 3 and combined_draws >= 2))
            and slug not in LOW_SCORING_TACTICAL_LEAGUE_SLUGS
            and not is_in_cooldown("btts_yes")
        ):
            selection = "Both Teams to Score ➔ Yes"
            alt_line = "Total ➔ Over 2.0 Goals"
            market_type = "btts"
            odds = 1.66
            ev_val = 14.8 + base_boost + strat_mod("btts_yes") + (2.0 if league_label in btts_pref else 0.0)
            why = f"Both teams score & concede regularly ({h_form or 'Attack'} vs {a_form or 'Attack'}); BTTS: Yes cashes on 1-1, 2-1, 1-2, and 2-2{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "goals_over_under",
                "selection": "Total: Over 1.5 Goals", "line": 1.5, "odds": 1.29
            }
            single = cls._build_single(date_str, home, away, market_type, selection, None, odds, 70.0, ev_val, why, league_label, bookie, kickoff_str, alt_line)
            return single, combo_leg

        # Strategy 3: Pure All-Out Shootout (Zero/Low Draw Profile, like Türkiye 1-2 Belgium `LLLLW vs LWLWL`) -> `Total ➔ Over 2.5 Goals`
        if (
            combined_draws <= 1
            and (h_recent_w + a_recent_w >= 2)
            and (h_recent_l + a_recent_l >= 4)
            and slug not in LOW_SCORING_TACTICAL_LEAGUE_SLUGS
            and league_label not in low_goal_traps
            and league_label not in btts_pref
            and not is_in_cooldown("over_25")
        ):
            odds = live_over_odds if (live_over_odds and 1.52 <= live_over_odds <= 1.95) else 1.68
            selection = "Total ➔ Over 2.5 Goals"
            alt_line = "Both Teams to Score ➔ Yes"
            market_type = "goals_over_under"
            ev_val = 14.0 + base_boost + strat_mod("over_25")
            why = f"All-or-nothing win/loss profile ({h_form} vs {a_form} — almost zero draws) projects 3+ match goals{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "goals_over_under",
                "selection": "Total: Over 1.5 Goals", "line": 1.5, "odds": 1.30
            }
            single = cls._build_single(date_str, home, away, market_type, selection, 2.5, odds, 68.5, ev_val, why, league_label, bookie, kickoff_str, alt_line)
            return single, combo_leg

        # Strategy 4: Strong Away Contender -> Auto-DNB in Tactical/2nd-Tier Leagues (`Leganés vs Burgos` Protection)
        if (a_recent_w >= 3 and a_recent_l <= 1 and a_win_rate >= h_win_rate + 0.14) or (
            live_away_odds and 1.52 <= live_away_odds <= 1.85
        ):
            if slug in LOW_SCORING_TACTICAL_LEAGUE_SLUGS or league_label in draw_traps or normalize_team_str(away) in unreliable_teams or is_in_cooldown("1x2_winner"):
                selection = f"Draw No Bet ➔ {away}"
                alt_line = f"Double Chance ➔ {away} or Draw (X2)"
                market_type = "dnb"
                odds = 1.58
                ev_val = 14.2 + base_boost + strat_mod("draw_no_bet")
                why = f"In-form {away} ({a_form}) protected with Draw No Bet (full refund if {home} holds a draw){buzz_tag}."
            else:
                odds = live_away_odds if (live_away_odds and 1.52 <= live_away_odds <= 1.95) else 1.65
                selection = f"1x2 ➔ {away} to Win"
                alt_line = f"Draw No Bet ➔ {away}"
                market_type = "1x2"
                ev_val = 14.0 + base_boost + strat_mod("1x2_winner")
                why = f"In-form {away} ({a_form or m.get('away_record') or 'Favored'}) vs struggling {home}{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "1x2",
                "selection": f"Double Chance: {away} or Draw (X2)", "line": None, "odds": 1.30
            }
            single = cls._build_single(date_str, home, away, market_type, selection, None, odds, 69.5, ev_val, why, league_label, bookie, kickoff_str, alt_line)
            return single, combo_leg

        # Strategy 5: Tactical / Low-Scoring League -> BC.Game `Total: Under 2.5 Goals`
        if slug in LOW_SCORING_TACTICAL_LEAGUE_SLUGS and league_label not in shootout_traps and not is_in_cooldown("under_25"):
            odds = live_under_odds if (live_under_odds and 1.52 <= live_under_odds <= 1.95) else 1.62
            selection = "Total ➔ Under 2.5 Goals"
            alt_line = f"Draw No Bet ➔ {home} (or Double Chance: 1X)"
            market_type = "goals_over_under"
            ev_val = 13.0 + base_boost + strat_mod("under_25")
            why = f"Tight tactical {league_label} clash (low-scoring profile averaging ~2.0 goals/gm); Under 2.5 is on BC.Game's main tab{buzz_tag}."
            combo_leg = {
                "home": home, "away": away, "market_type": "goals_over_under",
                "selection": "Total: Under 3.5 Goals", "line": 3.5, "odds": 1.26
            }
            single = cls._build_single(date_str, home, away, market_type, selection, 2.5, odds, 69.0, ev_val, why, league_label, bookie, kickoff_str, alt_line)
            return single, combo_leg

        # Strategy 6: Balanced Competitive Match -> BC.Game `Draw No Bet: {Home}`
        selection = f"Draw No Bet ➔ {home}"
        alt_line = "Both Teams to Score ➔ Yes"
        market_type = "dnb"
        odds = 1.58
        ev_val = 12.0 + base_boost + strat_mod("draw_no_bet")
        why = f"Home advantage in {league_label} with Draw No Bet protection (full stake refunded if match ends level){buzz_tag}."
        combo_leg = {
            "home": home, "away": away, "market_type": "1x2",
            "selection": f"Double Chance: {home} or Draw (1X)", "line": None, "odds": 1.28
        }
        single = cls._build_single(date_str, home, away, market_type, selection, None, odds, 68.5, ev_val, why, league_label, bookie, kickoff_str, alt_line)
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
        bookie: str,
        kickoff_str: str = "",
        alt_line: str = ""
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
            consensus_sources=["Footybett_Syndicate"],
            rationale=why,
            evidence=league_label,
            rotation_warning=None,
            search_url="",
            match_context=league_label,
            bookmaker_name=bookie,
            kickoff_str=kickoff_str,
            alt_bcgame_line=alt_line,
            is_combo=False
        )

    @classmethod
    def generate_slate_and_combo_for_active_date(cls) -> List[LedgerBetItem]:
        learning_state = SelfLearningEngine.recalibrate_from_ledger()

        active_date = DailyLedgerManager.get_active_date_str()
        existing = DailyLedgerManager.load_active_date_items()
        existing_singles = [i for i in existing if not i.is_combo]
        existing_combos = [i for i in existing if i.is_combo]

        if len(existing_singles) >= MAX_DAILY_SINGLES and len(existing_combos) >= 1:
            return existing

        buzz_teams = ChannelBuzzRadar.fetch_channel_buzz_teams()
        fixtures = LiveSportsbookAndStatsAPI.fetch_mens_fixtures_with_odds(active_date)
        next_day = shift_date_str(active_date, 1)
        fixtures.extend(LiveSportsbookAndStatsAPI.fetch_mens_fixtures_with_odds(next_day))

        paired_candidates: List[Tuple[int, int, float, LedgerBetItem, Dict[str, Any]]] = []
        for m in fixtures:
            single, c_leg = cls.analyze_match_for_single_and_combo_leg(
                m, active_date, buzz_teams, learning_state, max_hours_ahead=IDEAL_MAX_HOURS_BEFORE_KICKOFF
            )
            if single and single.odds >= MIN_SINGLE_ODDS and c_leg:
                odds_rank = 0 if m.get("has_live_odds") else 1
                paired_candidates.append((0, odds_rank, m.get("hours_until_kickoff") or 99.0, single, c_leg))

        if len(paired_candidates) < MAX_DAILY_SINGLES:
            already_picked = {p[3].bet_key for p in paired_candidates}
            for m in fixtures:
                single, c_leg = cls.analyze_match_for_single_and_combo_leg(
                    m, active_date, buzz_teams, learning_state, max_hours_ahead=ADAPTIVE_MAX_HOURS_BEFORE_KICKOFF
                )
                if single and single.odds >= MIN_SINGLE_ODDS and c_leg and single.bet_key not in already_picked:
                    already_picked.add(single.bet_key)
                    odds_rank = 0 if m.get("has_live_odds") else 1
                    paired_candidates.append((1, odds_rank, m.get("hours_until_kickoff") or 99.0, single, c_leg))

        paired_candidates.sort(key=lambda item: (item[0], item[1], -item[3].edge_ev, item[2]))
        top_pairs = paired_candidates[:MAX_DAILY_SINGLES]

        slots_left = MAX_DAILY_SINGLES - len(existing_singles)
        for _, _, _, single, _ in top_pairs[: max(0, slots_left)]:
            DailyLedgerManager.upsert_bet(single)

        updated_existing = DailyLedgerManager.load_active_date_items()
        current_singles = [i for i in updated_existing if not i.is_combo]

        if not existing_combos and len(current_singles) >= 2:
            combo_legs_pool: List[Dict[str, Any]] = []
            for s in current_singles:
                if "Under 2.5" in s.selection:
                    combo_legs_pool.append({
                        "home": s.team_home, "away": s.team_away, "market_type": "goals_over_under",
                        "selection": "Total: Under 3.5 Goals", "line": 3.5, "odds": 1.26
                    })
                elif s.market_type in ["1x2", "dnb"]:
                    is_away_fav = (s.team_away in s.selection) and (s.team_home not in s.selection)
                    dc_str = f"Double Chance: {s.team_away} or Draw (X2)" if is_away_fav else f"Double Chance: {s.team_home} or Draw (1X)"
                    combo_legs_pool.append({
                        "home": s.team_home, "away": s.team_away, "market_type": "1x2",
                        "selection": dc_str, "line": None, "odds": 1.28
                    })
                else:
                    combo_legs_pool.append({
                        "home": s.team_home, "away": s.team_away, "market_type": "goals_over_under",
                        "selection": "Total: Over 1.5 Goals", "line": 1.5, "odds": 1.29
                    })

            for _, _, _, _, c_leg in paired_candidates:
                if not any(teams_match(c_leg["home"], lg["home"]) for lg in combo_legs_pool):
                    combo_legs_pool.append(c_leg)
                if len(combo_legs_pool) >= 3:
                    break

            if len(combo_legs_pool) >= 2:
                chosen_legs = combo_legs_pool[:3]
                combined_odds = 1.0
                for lg in chosen_legs:
                    combined_odds *= float(lg.get("odds", 1.28))
                combined_odds = round(combined_odds, 2)

                leg_global_desc = " + ".join(
                    f"{lg['home']} vs {lg['away']} ({lg['selection']})" for lg in chosen_legs
                )
                legs_hash = hashlib.md5(leg_global_desc.encode("utf-8")).hexdigest()[:8]
                combo_item = LedgerBetItem(
                    bet_key=f"combo_{active_date}_{legs_hash}",
                    date_str=active_date,
                    team_home="DAILY BC.GAME SAFE COMBO",
                    team_away=f"({len(chosen_legs)} Main-Tab Legs)",
                    market_type="daily_parlay",
                    selection=leg_global_desc,
                    line=None,
                    odds=combined_odds,
                    floor_odds=1.60,
                    is_approved=True,
                    confidence_stars="⭐️⭐️⭐️⭐️⭐️",
                    model_prob=65.0,
                    edge_ev=26.0,
                    recommended_units=0.5,
                    consensus_sources=["Footybett_Combo"],
                    rationale="100% universal BC.Game main-tab cushions (Over 1.5 / Under 3.5 / Double Chance 1X-X2) combined into 1 ticket.",
                    evidence="BC.Game Safe Combo",
                    rotation_warning=None,
                    search_url="",
                    match_context="Daily Bonus Combo",
                    bookmaker_name="BC.Game",
                    is_combo=True,
                    combo_legs=chosen_legs
                )
                DailyLedgerManager.upsert_bet(combo_item)

        return DailyLedgerManager.load_active_date_items()


class BetSlipCardFormatter:
    """Simple, clean, BC.Game-ready cards + End-of-Day Channel Recap for @Footybett and @betyyyybot."""

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
                "🎟️ TODAY'S BC.GAME SAFE COMBO — @Footybett\n"
                "────────────────────────\n"
                f"{legs_block}\n"
                f"💰 Total Odds : {s.odds:.2f}  |  Stake: {s.recommended_units:.1f}u (Bonus)\n"
                f"📊 Why        : {s.rationale}"
            )
        kickoff_line = f"\n⏰ Kickoff : {s.kickoff_str}" if s.kickoff_str else ""
        alt_line = f"\n🔄 Backup  : {s.alt_bcgame_line}" if s.alt_bcgame_line else ""
        return (
            "🟢 OPEN SINGLE BET — @Footybett\n"
            "────────────────────────\n"
            f"⚽ Match   : {s.team_home} vs {s.team_away} ({s.match_context}){kickoff_line}\n"
            f"🎯 BC.Game : {s.selection}\n"
            f"💰 Odds    : {s.odds:.2f}  |  Stake: {s.recommended_units:.1f}u{alt_line}\n"
            f"📊 Why     : {s.rationale}"
        )

    @classmethod
    def format_closed_bet_card(cls, s: LedgerBetItem) -> str:
        won, lost, wr, net_u = cls.get_totals_summary_tuple()
        label = "COMBO" if s.is_combo else "BET"
        match_line = (
            f"🎟️ Legs   : {s.score_str}"
            if s.is_combo
            else f"⚽ {s.team_home} vs {s.team_away} ➔ {s.score_str}"
        )
        if "WON" in s.settlement:
            prof = s.recommended_units * (s.odds - 1.0)
            return (
                f"✅ {label} CLOSED — WON (+{prof:.2f}u)\n"
                "────────────────────────\n"
                f"{match_line}\n"
                f"🎯 Bet    : {s.selection} @ {s.odds:.2f} ✅\n"
                f"📈 Record : {won}W - {lost}L ({wr:.0f}%) | {net_u:+.2f}u"
            )
        else:
            autopsy_line = f"\n{s.loss_autopsy}" if s.loss_autopsy else ""
            return (
                f"❌ {label} CLOSED — LOST (-{s.recommended_units:.2f}u)\n"
                "────────────────────────\n"
                f"{match_line}\n"
                f"🎯 Bet    : {s.selection} @ {s.odds:.2f} ❌{autopsy_line}\n"
                f"📈 Record : {won}W - {lost}L ({wr:.0f}%) | {net_u:+.2f}u"
            )

    @classmethod
    def format_end_of_day_channel_recap(cls, target_date: str) -> str:
        all_items = list(DailyLedgerManager.load_all_history_items().values())
        day_items = [i for i in all_items if i.date_str == target_date and i.is_approved]
        day_items.sort(key=lambda x: (1 if x.is_combo else 0))

        d_won = sum(1 for i in day_items if "WON" in i.settlement)
        d_lost = sum(1 for i in day_items if "LOST" in i.settlement)
        d_net = 0.0
        for i in day_items:
            if "WON" in i.settlement:
                d_net += i.recommended_units * (i.odds - 1.0)
            elif "LOST" in i.settlement:
                d_net -= i.recommended_units

        won_all, lost_all, wr_all, net_all = cls.get_totals_summary_tuple()

        lines = [
            f"📊 END OF DAY RESULTS — @Footybett ({target_date})",
            "────────────────────────"
        ]
        for idx, s in enumerate(day_items, 1):
            label = "🎟️ SAFE COMBO" if s.is_combo else f"⚽ {s.team_home} vs {s.team_away}"
            if "WON" in s.settlement:
                p_u = s.recommended_units * (s.odds - 1.0)
                lines.append(f"{idx}. ✅ {label} ➔ {s.selection} @ {s.odds:.2f} (+{p_u:.2f}u)")
            elif "LOST" in s.settlement:
                lines.append(f"{idx}. ❌ {label} ➔ {s.selection} @ {s.odds:.2f} (-{s.recommended_units:.2f}u)")
                if s.loss_autopsy:
                    lines.append(f"   ↳ {s.loss_autopsy}")
            else:
                lines.append(f"{idx}. ➖ {label} ➔ {s.selection} @ {s.odds:.2f} (PUSH / +0.00u)")

        lines.extend([
            "────────────────────────",
            f"📅 Day Result   : {d_won} Won ✅ | {d_lost} Lost ❌ ({d_net:+.2f}u)",
            f"📈 Total Record : {won_all}W - {lost_all}L ({wr_all:.1f}% Win Rate)",
            f"💰 Total Profit : {net_all:+.2f} Units ( @ $50/u = ${net_all * 50:+.2f} )",
            "────────────────────────",
            "🔔 Model Weights Updated • Next Pre-Kickoff Slate Tomorrow"
        ])
        return "\n".join(lines)

    @classmethod
    def format_clean_today_and_total(cls) -> str:
        active_date = DailyLedgerManager.get_active_date_str()
        yesterday_date = DailyLedgerManager.get_yesterday_str()
        items = DailyLedgerManager.load_active_date_items()
        y_items = DailyLedgerManager.load_yesterday_items()
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
            f"🎯 TODAY'S BC.GAME SINGLE BETS ({active_date})",
            "────────────────────────"
        ]

        if singles:
            for idx, s in enumerate(singles, 1):
                st_icon = "✅ WON" if "WON" in s.settlement else ("❌ LOST" if "LOST" in s.settlement else "🟢 OPEN")
                sc = f" | {s.score_str}" if s.score_str != "-" else ""
                ko = f" [{s.kickoff_str}]" if s.kickoff_str else ""
                lines.append(f"{idx}. [{st_icon}{sc}] {s.team_home} vs {s.team_away} ({s.match_context}){ko}")
                lines.append(f"   🎯 BC.Game: {s.selection} @ {s.odds:.2f} (1.0u)")
                if s.alt_bcgame_line:
                    lines.append(f"   🔄 Backup : {s.alt_bcgame_line}")
                lines.append(f"   💡 {s.rationale}")
                if s.loss_autopsy:
                    lines.append(f"   {s.loss_autopsy}")
        else:
            lines.append("• Queue active: Waiting for today's matches to enter the 2.5h–5.5h pre-kickoff window.")

        if combos:
            c = combos[0]
            st_icon = "✅ WON" if "WON" in c.settlement else ("❌ LOST" if "LOST" in c.settlement else "🎟️ OPEN")
            lines.append("")
            lines.append(f"🎟️ TODAY'S BC.GAME SAFE COMBO [{st_icon}] — Total Odds: {c.odds:.2f} (0.5u):")
            for lg in (c.combo_legs or []):
                lines.append(f"   • {lg['home']} vs {lg['away']} ➔ {lg['selection']} (@ {lg['odds']:.2f})")

        if y_items:
            y_won = sum(1 for i in y_items if "WON" in i.settlement)
            y_lost = sum(1 for i in y_items if "LOST" in i.settlement)
            lines.append("")
            lines.append(f"📅 YESTERDAY'S AUDIT ({yesterday_date}: {y_won}W - {y_lost}L):")
            for yi in y_items:
                st_ic = "✅" if "WON" in yi.settlement else ("❌" if "LOST" in yi.settlement else "⏳")
                name_str = "DAILY COMBO" if yi.is_combo else f"{yi.team_home} vs {yi.team_away}"
                lines.append(f"   {st_ic} {name_str} — {yi.selection} @ {yi.odds:.2f} ➔ {yi.score_str}")
                if yi.loss_autopsy:
                    lines.append(f"      ↳ {yi.loss_autopsy}")

        lines.extend([
            "",
            f"📊 TOTAL RECORD (Since {TRACKING_START_DATE})",
            "────────────────────────",
            f"• Today : {d_won}W - {d_lost}L ({d_open} Open) | {d_net:+.2f}u",
            f"• Total : {won_all}W - {lost_all}L ({wr_all:.1f}%) | {net_all:+.2f}u (${net_all * 50:+.2f})",
            "• Brain : Deep Match-Autopsy v18.3 Active (Tap /learn)"
        ])
        return "\n".join(lines)


class TelegramBotClient:
    REMOVE_BOTTOM_KEYBOARD = {"remove_keyboard": True}

    def __init__(self, bot_token: str):
        self.bot_token = bot_token.strip()
        self.base_url = f"https://api.telegram.org/bot{self.bot_token}"
        self.channel_publish_lock = threading.Lock()
        DailyLedgerManager.load_all_history_items()
        SelfLearningEngine.recalibrate_from_ledger()

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
            LiveSportsbookAndStatsAPI.grade_ledger_items()
            SafeCushionBetCreator.generate_slate_and_combo_for_active_date()
            all_items = DailyLedgerManager.load_all_history_items()
            active_date = DailyLedgerManager.get_active_date_str()
            yesterday_date = DailyLedgerManager.get_yesterday_str()
            published_count = 0
            updated = False

            ordered_items = sorted(all_items.items(), key=lambda kv: (1 if kv[1].is_combo else 0))

            for full_key, item in ordered_items:
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

            for check_d in sorted({yesterday_date, active_date}):
                if check_d < TRACKING_START_DATE:
                    continue
                day_picks = [
                    i for i in all_items.values()
                    if i.date_str == check_d and i.is_approved and i.published_to_channel
                ]
                if not day_picks:
                    continue
                settled_day = [i for i in day_picks if i.settlement in ["WON ✅", "LOST ❌", "PUSH ➖"]]
                if len(settled_day) == len(day_picks) and len(settled_day) >= 2:
                    eod_lock_key = f"eod_recap:{check_d}:{len(settled_day)}"
                    if not DailyLedgerManager.is_locked_in_channel(eod_lock_key):
                        recap_card = BetSlipCardFormatter.format_end_of_day_channel_recap(check_d)
                        if self.send_message(PUBLISH_CHANNEL_ID, recap_card, remove_kb=False):
                            DailyLedgerManager.mark_locked_in_channel(eod_lock_key)
                            time.sleep(1.0)

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
        logger.info("Footybett v18.3 Deep Match-Autopsy Worker started...")
        time.sleep(3)
        while True:
            try:
                self.sync_and_publish_to_footybett()
            except Exception as e:
                logger.error("Background worker error: %s", e)
            time.sleep(60)

    def set_official_menu_commands(self):
        commands = [
            {"command": "scan", "description": "🎯 Today's Singles, Combo & Yesterday Audit"},
            {"command": "results", "description": "🏁 Refresh Live Scores & Outcomes"},
            {"command": "learn", "description": "🧠 View Match Autopsies & Learned Rules"},
            {"command": "stats", "description": "📈 Total Record & P&L (From 2026-11-11)"},
            {"command": "poststats", "description": "📢 Post End-of-Day Recap to @Footybett"}
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

        logger.info("Bot listener running (v18.3 Deep Match-Autopsy Engine)...")
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

                if text == "/learn":
                    def handle_learn(cid):
                        self.sync_and_publish_to_footybett()
                        self.send_message(cid, SelfLearningEngine.format_learning_report())
                    threading.Thread(target=handle_learn, args=[chat_id], daemon=True).start()
                    continue

                if text == "/poststats":
                    def handle_post_stats(cid):
                        self.sync_and_publish_to_footybett()
                        target_d = DailyLedgerManager.get_active_date_str()
                        if not DailyLedgerManager.load_active_date_items():
                            target_d = DailyLedgerManager.get_yesterday_str()
                        recap = BetSlipCardFormatter.format_end_of_day_channel_recap(target_d)
                        if self.send_message(PUBLISH_CHANNEL_ID, recap, remove_kb=False):
                            self.send_message(cid, f"✅ Sent End-of-Day Recap to {PUBLISH_CHANNEL_ID}!\n\n{recap}")
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