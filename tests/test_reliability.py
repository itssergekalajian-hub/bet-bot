import json
import tempfile
import threading
import unittest
from pathlib import Path
from types import SimpleNamespace

import telegram_bet_analyzer_bot as bot


class ReliabilityTests(unittest.TestCase):
    def test_atomic_json_writes_remain_valid_under_concurrent_writes(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "daily_ledger.json"
            bot._atomic_write_json(path, {"worker": -1, "index": -1})
            stop_reader = threading.Event()
            reader_ready = threading.Event()
            read_errors = []
            write_errors = []

            def read_values():
                while not stop_reader.is_set():
                    value = bot.load_json_dict(path)
                    if not value or not isinstance(value.get("worker"), int):
                        read_errors.append(value)
                    reader_ready.set()

            def write_values(worker_id):
                try:
                    for index in range(20):
                        bot._atomic_write_json(path, {"worker": worker_id, "index": index})
                except Exception as exc:
                    write_errors.append(exc)

            reader = threading.Thread(target=read_values)
            reader.start()
            self.assertTrue(reader_ready.wait(timeout=2))
            threads = [
                threading.Thread(target=write_values, args=(worker_id,))
                for worker_id in range(4)
            ]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
            stop_reader.set()
            reader.join()

            with path.open(encoding="utf-8") as file:
                final_value = json.load(file)
            self.assertIn(final_value["worker"], range(4))
            self.assertIn(final_value["index"], range(20))
            self.assertFalse(read_errors)
            self.assertFalse(write_errors)
            self.assertFalse(any(file.suffix == ".tmp" for file in Path(temp_dir).iterdir()))

    def test_settlement_waits_until_103_minutes_after_kickoff(self):
        item = SimpleNamespace(
            is_combo=False,
            kickoff_epoch=1_000_000.0,
            published_at_epoch=1_000_000.0,
            date_str="",
            kickoff_str="",
            settlement="WON ✅",
            manual_settled=False,
        )
        self.assertFalse(
            bot.LiveSportsbookAndStatsAPI.is_item_physically_allowed_to_settle(
                item, now_epoch=1_000_000.0 + 103 * 60 - 1
            )
        )
        self.assertTrue(
            bot.LiveSportsbookAndStatsAPI.is_item_physically_allowed_to_settle(
                item, now_epoch=1_000_000.0 + 103 * 60
            )
        )

    def test_long_lotto_message_html_is_at_most_4096_characters(self):
        rendered = bot.render_telegram_html("lotto " * 2000)
        self.assertLessEqual(len(rendered), 4096)

    def test_http_sessions_use_sized_connection_pools(self):
        session = bot._get_http_session()
        for scheme in ("http://", "https://"):
            adapter = session.get_adapter(scheme)
            self.assertEqual(adapter._pool_connections, 16)
            self.assertEqual(adapter._pool_maxsize, 16)


if __name__ == "__main__":
    unittest.main()
