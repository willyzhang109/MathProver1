"""Determine the real client IP without letting anyone forge it.

X-Forwarded-For is attacker-controlled unless the immediate peer is a proxy we
put there ourselves, so it is consulted only when the peer is in
TRUSTED_PROXIES. Otherwise the peer address is used and the header ignored.

Requires nginx `proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for`
(which appends the peer it sees), and uvicorn started WITHOUT --proxy-headers
and with --forwarded-allow-ips="" -- otherwise uvicorn rewrites request.client
from the header before this code ever runs.
"""

from ipaddress import ip_address, ip_network
from typing import List, Optional

from .config import settings

_NETS = None


def _trusted_nets() -> List:
    global _NETS
    if _NETS is None:
        nets = []
        for entry in settings.trusted_proxies:
            try:
                nets.append(ip_network(entry, strict=False))
            except ValueError:
                continue
        _NETS = nets
    return _NETS


def _parse(raw: str) -> Optional[str]:
    raw = raw.strip()
    if not raw:
        return None
    # Strip brackets/port forms: "[::1]:443", "1.2.3.4:5678"
    if raw.startswith("["):
        raw = raw[1:].split("]")[0]
    elif raw.count(":") == 1 and "." in raw:
        raw = raw.split(":")[0]
    try:
        return str(ip_address(raw))
    except ValueError:
        return None


def is_trusted(addr: str) -> bool:
    try:
        parsed = ip_address(addr)
    except ValueError:
        return False
    return any(parsed in net for net in _trusted_nets())


def client_ip(peer: Optional[str], headers) -> str:
    """Resolve the client address from the peer and forwarding headers."""
    peer = _parse(peer or "") or "0.0.0.0"

    if not is_trusted(peer):
        return peer  # header ignored entirely

    if settings.trust_x_real_ip:
        real = _parse(headers.get("x-real-ip") or "")
        if real:
            return real

    xff = headers.get("x-forwarded-for")
    if not xff:
        return peer

    chain = [addr for addr in (_parse(part) for part in xff.split(",")) if addr]
    for addr in reversed(chain):
        if not is_trusted(addr):
            return addr
    return chain[0] if chain else peer


def bucket(addr: str) -> str:
    """Group addresses into a rate-limit key.

    IPv4 is used as-is. IPv6 collapses to /56: a single subscriber is routinely
    delegated a whole /64 or /56, so limiting per-address would be free to
    bypass by picking a new suffix.
    """
    try:
        parsed = ip_address(addr)
    except ValueError:
        return addr
    if parsed.version == 4:
        return f"{parsed}/32"
    return str(ip_network(f"{parsed}/56", strict=False))
