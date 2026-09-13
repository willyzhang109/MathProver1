"""Sliding-window request limiting, per IP bucket and per class."""

import time
from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Dict, Tuple

from .config import settings


@dataclass
class Decision:
    allowed: bool
    limit: int
    remaining: int
    retry_after_s: int
    reset_at: float


class RateLimiter:
    def __init__(self):
        self._hits: Dict[Tuple[str, str], deque] = defaultdict(deque)
        self._day: deque = deque()

    def _limit_for(self, klass: str) -> int:
        return {
            "job": settings.limit_job,
            "formalize": settings.limit_formalize,
            "check": settings.limit_check,
            "read": settings.limit_read,
        }.get(klass, settings.limit_read)

    def peek(self, key: str, klass: str, now: float = None) -> Decision:
        """Report the current state without consuming a slot."""
        now = now if now is not None else time.time()
        window = settings.rate_window_s
        limit = self._limit_for(klass)

        hits = self._hits[(key, klass)]
        while hits and hits[0] <= now - window:
            hits.popleft()

        if len(hits) < limit:
            return Decision(True, limit, limit - len(hits), 0, now + window)

        oldest = hits[0]
        retry = max(1, int(window - (now - oldest)) + 1)
        return Decision(False, limit, 0, retry, oldest + window)

    def check(self, key: str, klass: str, now: float = None) -> Decision:
        """Consume a slot when one is available."""
        now = now if now is not None else time.time()
        decision = self.peek(key, klass, now)
        if decision.allowed:
            self._hits[(key, klass)].append(now)
            decision.remaining -= 1
        return decision

    def check_global_daily(self, now: float = None) -> bool:
        """Service-wide backstop: IP limits are defeated by any VPN, and the
        real exposure here is the Gemini bill."""
        now = now if now is not None else time.time()
        cap = settings.max_jobs_per_day
        if cap <= 0:
            return True
        while self._day and self._day[0] <= now - 86400:
            self._day.popleft()
        if len(self._day) >= cap:
            return False
        self._day.append(now)
        return True

    def sweep(self, now: float = None) -> int:
        """Drop empty deques so the dict cannot grow without bound."""
        now = now if now is not None else time.time()
        window = settings.rate_window_s
        dead = []
        for key, hits in self._hits.items():
            while hits and hits[0] <= now - window:
                hits.popleft()
            if not hits:
                dead.append(key)
        for key in dead:
            del self._hits[key]
        return len(dead)


limiter = RateLimiter()
