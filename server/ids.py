"""Time-sortable, unguessable identifiers."""

import secrets
import time


def new_id(prefix: str = "job") -> str:
    stamp = format(int(time.time()), "x")
    return f"{prefix}_{stamp}_{secrets.token_hex(8)}"
