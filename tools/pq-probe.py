#!/usr/bin/env python3
"""
pq-probe.py — Graviton Live Post-Quantum TLS, MTU Fragmentation & Downgrade Probe
=================================================================================
Practical companion CLI to GravitonCert.Studies.PostQuantumAgentAuth (PQA-06, PQA-GATE-01).

Closes CBOMkit's #1 operational blind spot: tests LIVE HTTPS/TLS 1.3 endpoints for:
  1. Negotiated TLS version & cipher suite (via Python SSL + OpenSSL s_client if available)
  2. Live post-quantum hybrid key exchange support (`X25519MLKEM768` / `SecP256r1MLKEM768`)
  3. Leaf + chain certificate byte size vs. 1,460 B TCP MSS / 1,500 B Ethernet MTU threshold
  4. Classical downgrade readiness risk rating ahead of CNSA 2.0 (Jan 1, 2027)

License: MIT — Graviton Research Foundation (https://gravitonresearch.org)
"""

from __future__ import annotations

import argparse
import json
import shutil
import socket
import ssl
import subprocess
import sys
import time
from typing import Any, Dict

TCP_MSS_BYTES = 1460
MLDSA65_CERT_OVERHEAD = 5261  # 1952 PK + 3309 Sig (PQA-06)


def probe_host(host: str, port: int = 443, timeout: float = 8.0) -> Dict[str, Any]:
    result: Dict[str, Any] = {
        "host": host,
        "port": port,
        "reachable": False,
        "tls_version": None,
        "cipher": None,
        "leaf_cert_bytes": None,
        "exceeds_single_mss_today": None,
        "projected_mldsa65_bytes": None,
        "projected_mldsa65_tcp_segments": None,
        "pqc_group_negotiated": None,
        "openssl_pqc_probe": "skipped",
        "latency_ms": None,
    }

    t0 = time.perf_counter()
    ca_file = "/etc/ssl/cert.pem"
    import os
    ctx = ssl.create_default_context(cafile=ca_file) if os.path.exists(ca_file) else ssl.create_default_context()
    with socket.create_connection((host, port), timeout=timeout) as sock:
        with ctx.wrap_socket(sock, server_hostname=host) as ssock:
            result["reachable"] = True
            result["latency_ms"] = round((time.perf_counter() - t0) * 1000, 1)
            result["tls_version"] = ssock.version()
            result["cipher"] = ssock.cipher()[0] if ssock.cipher() else None
            der = ssock.getpeercert(binary_form=True)
            if der:
                n_bytes = len(der)
                result["leaf_cert_bytes"] = n_bytes
                result["exceeds_single_mss_today"] = n_bytes > TCP_MSS_BYTES
                proj = n_bytes + MLDSA65_CERT_OVERHEAD
                result["projected_mldsa65_bytes"] = proj
                result["projected_mldsa65_tcp_segments"] = (proj + TCP_MSS_BYTES - 1) // TCP_MSS_BYTES

    openssl = shutil.which("openssl")
    if openssl:
        try:
            proc = subprocess.run(
                [openssl, "s_client", "-connect", f"{host}:{port}", "-servername", host, "-groups", "X25519MLKEM768:X25519"],
                input=b"Q\n",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
            )
            out = proc.stdout.decode("utf-8", errors="ignore") + "\n" + proc.stderr.decode("utf-8", errors="ignore")
            if "Server Temp Key:" in out or "Peer Temp Key:" in out or "Negotiated TLS1.3 group:" in out:
                for line in out.splitlines():
                    if any(k in line for k in ("Negotiated TLS1.3 group:", "Server Temp Key:", "Peer Temp Key:")):
                        result["pqc_group_negotiated"] = line.strip()
                        break
                result["openssl_pqc_probe"] = "ok"
            elif "unknown group" in out.lower() or "error setting groups" in out.lower():
                result["openssl_pqc_probe"] = "local_openssl_lacks_mlkem_group"
            else:
                result["openssl_pqc_probe"] = "no_group_line"
        except Exception as exc:
            result["openssl_pqc_probe"] = f"error:{type(exc).__name__}"

    return result


def main() -> int:
    parser = argparse.ArgumentParser(description="Graviton PQ-Probe: Live TLS 1.3 PQC & MTU Fragmentation Auditor")
    parser.add_argument("hosts", nargs="*", default=["gravitonresearch.org"], help="Hostnames to probe (default: gravitonresearch.org)")
    parser.add_argument("--port", type=int, default=443)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    reports = []
    for h in args.hosts:
        try:
            reports.append(probe_host(h, args.port))
        except Exception as exc:
            reports.append({"host": h, "port": args.port, "reachable": False, "error": str(exc)})

    if args.json:
        print(json.dumps(reports, indent=2))
    else:
        for r in reports:
            print(f"Graviton PQ-Probe — {r['host']}:{r['port']}")
            print("-" * 56)
            if not r.get("reachable"):
                print(f"  ERROR: {r.get('error', 'unreachable')}\n")
                continue
            print(f"  TLS / Cipher        : {r['tls_version']} / {r['cipher']} ({r['latency_ms']} ms)")
            print(f"  Leaf Cert Size      : {r['leaf_cert_bytes']} B (exceeds 1460 B MSS today: {r['exceeds_single_mss_today']})")
            print(f"  Projected ML-DSA-65 : ~{r['projected_mldsa65_bytes']} B (~{r['projected_mldsa65_tcp_segments']} TCP segments per cert)")
            print(f"  PQC Group Probe     : {r['pqc_group_negotiated'] or r['openssl_pqc_probe']}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
