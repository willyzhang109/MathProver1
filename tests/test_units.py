"""Unit tests for the pieces that need no Lean toolchain."""

import sys, time, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from server.clientip import client_ip, bucket, is_trusted
from server.ratelimit import RateLimiter
from server.config import settings


class Headers(dict):
    def get(self, key, default=None):
        return dict.get(self, key.lower(), default)


class TestClientIP(unittest.TestCase):
    def test_untrusted_peer_xff_ignored(self):
        # The whole point: a direct caller cannot claim to be someone else.
        got = client_ip("203.0.113.9", Headers({"x-forwarded-for": "1.2.3.4"}))
        self.assertEqual(got, "203.0.113.9")

    def test_trusted_peer_uses_rightmost_untrusted(self):
        got = client_ip("127.0.0.1", Headers({"x-forwarded-for": "1.2.3.4, 198.51.100.7"}))
        self.assertEqual(got, "198.51.100.7")

    def test_spoofed_prefix_behind_proxy_does_not_win(self):
        # Client sends "9.9.9.9"; nginx appends the true peer on the right.
        got = client_ip("127.0.0.1", Headers({"x-forwarded-for": "9.9.9.9, 198.51.100.7"}))
        self.assertEqual(got, "198.51.100.7")

    def test_trusted_peer_no_header(self):
        self.assertEqual(client_ip("127.0.0.1", Headers()), "127.0.0.1")

    def test_port_and_bracket_forms(self):
        self.assertEqual(client_ip("1.2.3.4:5678", Headers()), "1.2.3.4")
        self.assertEqual(client_ip("[::1]", Headers({"x-forwarded-for": "2001:db8::5"})),
                         "2001:db8::5")

    def test_garbage_header_falls_back(self):
        got = client_ip("127.0.0.1", Headers({"x-forwarded-for": "not-an-ip, ,"}))
        self.assertEqual(got, "127.0.0.1")

    def test_all_trusted_chain(self):
        got = client_ip("127.0.0.1", Headers({"x-forwarded-for": "127.0.0.1, ::1"}))
        self.assertEqual(got, "127.0.0.1")

    def test_is_trusted(self):
        self.assertTrue(is_trusted("127.0.0.1"))
        self.assertFalse(is_trusted("8.8.8.8"))


class TestBucket(unittest.TestCase):
    def test_ipv4_exact(self):
        self.assertEqual(bucket("203.0.113.9"), "203.0.113.9/32")

    def test_ipv6_same_56_shares_bucket(self):
        a = bucket("2001:db8:abcd:ee00::1")
        b = bucket("2001:db8:abcd:eeff::9999")
        self.assertEqual(a, b)

    def test_ipv6_different_56_differs(self):
        self.assertNotEqual(bucket("2001:db8:abcd:0100::1"),
                            bucket("2001:db8:abcd:ff00::1"))


class TestRateLimit(unittest.TestCase):
    def setUp(self):
        self.rl = RateLimiter()
        self.t = 1_000_000.0

    def test_three_then_denied(self):
        for i in range(settings.limit_job):
            d = self.rl.check("k", "job", self.t + i)
            self.assertTrue(d.allowed, f"request {i} should be allowed")
        d = self.rl.check("k", "job", self.t + 3)
        self.assertFalse(d.allowed)
        self.assertEqual(d.limit, 3)
        self.assertEqual(d.remaining, 0)

    def test_retry_after_counts_from_oldest(self):
        for i in range(3):
            self.rl.check("k", "job", self.t + i)
        d = self.rl.check("k", "job", self.t + 100)
        # oldest was at t+0, window 3600 -> ~3500s left
        self.assertAlmostEqual(d.retry_after_s, 3501, delta=2)

    def test_window_expiry_frees_a_slot(self):
        for i in range(3):
            self.rl.check("k", "job", self.t + i)
        later = self.t + settings.rate_window_s + 1
        self.assertTrue(self.rl.check("k", "job", later).allowed)

    def test_classes_are_independent(self):
        for i in range(3):
            self.rl.check("k", "job", self.t + i)
        self.assertFalse(self.rl.check("k", "job", self.t).allowed)
        self.assertTrue(self.rl.check("k", "check", self.t).allowed)

    def test_buckets_are_independent(self):
        for i in range(3):
            self.rl.check("a", "job", self.t + i)
        self.assertTrue(self.rl.check("b", "job", self.t).allowed)

    def test_peek_does_not_consume(self):
        self.rl.peek("k", "job", self.t)
        self.rl.peek("k", "job", self.t)
        self.assertTrue(self.rl.check("k", "job", self.t).allowed)

    def test_sweep_drops_stale(self):
        self.rl.check("k", "job", self.t)
        self.assertEqual(self.rl.sweep(self.t + settings.rate_window_s + 1), 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
