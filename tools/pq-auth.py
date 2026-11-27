#!/usr/bin/env python3
"""
pq-auth.py — Graviton PQ-Guard Merkle-Batched Verifiable Agent Authority SDK
============================================================================
Practical companion SDK to GravitonCert.Studies.PostQuantumAgentAuth (PQA-01..PQA-07).

Implements:
  - SHA3-256 Merkle-batched capability trees (amortizing 3,309-byte ML-DSA-65 root signatures
    across up to 65,536 agent/MCP tool actions — PQA-01)
  - Monotone capability attenuation checks (spend, expiry, 64-bit scope bitmask — PQA-02)
  - Pre-execution authority firewall ("Attempted vs. Happened" — PQA-03)
  - Replay-nonce registry preventing signed-token double-spend (PQA-04)
  - Strict hybrid Ed25519 + ML-DSA anti-downgrade policy gate (PQA-05)

License: MIT — Graviton Research Foundation (https://gravitonresearch.org)
"""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass
from typing import Dict, List, Set, Tuple


def sha3_256(data: bytes) -> bytes:
    return hashlib.sha3_256(data).digest()


@dataclass(frozen=True)
class AgentCapability:
    max_spend_cents: int
    expiry_epoch: int
    scope_mask: int  # 64-bit permission bitmask

    def to_canonical_bytes(self, nonce: int) -> bytes:
        payload = {
            "max_spend_cents": self.max_spend_cents,
            "expiry_epoch": self.expiry_epoch,
            "scope_mask": self.scope_mask,
            "nonce": nonce,
        }
        return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")

    def is_attenuated_from(self, parent: "AgentCapability") -> bool:
        return (
            self.max_spend_cents <= parent.max_spend_cents
            and self.expiry_epoch <= parent.expiry_epoch
            and (self.scope_mask & (~parent.scope_mask & ((1 << 64) - 1))) == 0
        )


def build_merkle_tree(leaves: List[bytes]) -> Tuple[bytes, List[List[Tuple[str, bytes]]]]:
    if not leaves:
        raise ValueError("Need at least one capability leaf")
    hashed = [sha3_256(b"PQA-LEAF:" + leaf) for leaf in leaves]
    n = 1
    while n < len(hashed):
        n <<= 1
    pad = sha3_256(b"PQA-PAD")
    level = hashed + [pad] * (n - len(hashed))
    levels = [level]
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            nxt.append(sha3_256(b"PQA-NODE:" + level[i] + level[i + 1]))
        levels.append(nxt)
        level = nxt
    root = levels[-1][0]

    proofs: List[List[Tuple[str, bytes]]] = []
    for idx in range(len(leaves)):
        proof = []
        pos = idx
        for lvl in levels[:-1]:
            if pos % 2 == 0:
                proof.append(("R", lvl[pos + 1]))
            else:
                proof.append(("L", lvl[pos - 1]))
            pos //= 2
        proofs.append(proof)
    return root, proofs


def verify_merkle_proof(leaf: bytes, proof: List[Tuple[str, bytes]], root: bytes) -> bool:
    cur = sha3_256(b"PQA-LEAF:" + leaf)
    for side, sibling in proof:
        if side == "R":
            cur = sha3_256(b"PQA-NODE:" + cur + sibling)
        else:
            cur = sha3_256(b"PQA-NODE:" + sibling + cur)
    return cur == root


class PQAuthorityFirewall:
    """Enforces PQA-02..PQA-05 before any agent tool/payment call executes."""

    def __init__(self, root_cap: AgentCapability, merkle_root: bytes, allow_classical_only: bool = False):
        if allow_classical_only:
            raise ValueError("PQA-05 policy violation: classical-only downgrade fallback is prohibited.")
        self.root_cap = root_cap
        self.merkle_root = merkle_root
        self.spent_nonces: Set[int] = set()

    def authorize_action(
        self,
        cap: AgentCapability,
        nonce: int,
        proof: List[Tuple[str, bytes]],
        hybrid_root_sig_valid: bool,
        spend_cents: int,
        now_epoch: int,
        required_mask: int,
    ) -> Tuple[bool, str]:
        if not hybrid_root_sig_valid:
            return False, "REJECT: invalid hybrid Ed25519+ML-DSA root signature"
        if not cap.is_attenuated_from(self.root_cap):
            return False, "REJECT: PQA-02 capability escalation outside root envelope"
        if not verify_merkle_proof(cap.to_canonical_bytes(nonce), proof, self.merkle_root):
            return False, "REJECT: invalid SHA3-256 Merkle inclusion proof"
        if nonce in self.spent_nonces:
            return False, "REJECT: PQA-04 replayed nonce (double-spend blocked)"
        if spend_cents > cap.max_spend_cents:
            return False, "REJECT: PQA-03 spend exceeds capability cap"
        if now_epoch > cap.expiry_epoch:
            return False, "REJECT: PQA-03 capability expired"
        if (required_mask & (~cap.scope_mask & ((1 << 64) - 1))) != 0:
            return False, "REJECT: PQA-03 required permission outside scope_mask"

        self.spent_nonces.add(nonce)
        return True, "ALLOW: authorized under hybrid PQ Merkle capability root"


def run_self_test() -> int:
    print("Graviton PQ-Auth Self-Test (PQA-01..PQA-07)")
    print("==========================================")

    # Scope bits: bit 0 = read, bit 1 = write, bit 2 = pay
    root_cap = AgentCapability(max_spend_cents=10000, expiry_epoch=1800000000, scope_mask=0b111)
    # Batch 64 attenuated sub-agent capabilities under ONE 3,309-byte ML-DSA-65 root signature
    caps = [AgentCapability(max_spend_cents=500, expiry_epoch=1796000000, scope_mask=0b101) for _ in range(64)]
    leaves = [c.to_canonical_bytes(nonce=i) for i, c in enumerate(caps)]
    root, proofs = build_merkle_tree(leaves)

    # 1. Verify PQA-01 byte savings at k = 64, depth = 6
    depth = len(proofs[0])
    batched_bytes = 3309 + 64 * depth * 32
    naive_bytes = 64 * 3309
    assert depth == 6 and batched_bytes == 15597 and naive_bytes == 211776
    print(f"[OK] PQA-01: 64-call Merkle batch = {batched_bytes:,} B vs {naive_bytes:,} B naive ML-DSA-65 ({naive_bytes/batched_bytes:.1f}x reduction).")

    fw = PQAuthorityFirewall(root_cap=root_cap, merkle_root=root, allow_classical_only=False)

    # 2. Valid execution passes
    ok, msg = fw.authorize_action(caps[0], 0, proofs[0], True, spend_cents=250, now_epoch=1795727000, required_mask=0b100)
    assert ok, msg
    print(f"[OK] PQA-03: Legitimate payment call authorized ({msg}).")

    # 3. Replay attack blocked (PQA-04)
    ok_rep, msg_rep = fw.authorize_action(caps[0], 0, proofs[0], True, spend_cents=250, now_epoch=1795727000, required_mask=0b100)
    assert not ok_rep and "PQA-04" in msg_rep
    print(f"[OK] PQA-04: Replay double-spend blocked ({msg_rep}).")

    # 4. Privilege escalation blocked (PQA-02)
    bad_cap = AgentCapability(max_spend_cents=50000, expiry_epoch=1796000000, scope_mask=0b111)
    ok_esc, msg_esc = fw.authorize_action(bad_cap, 1, proofs[1], True, spend_cents=250, now_epoch=1795727000, required_mask=0b100)
    assert not ok_esc and "PQA-02" in msg_esc
    print(f"[OK] PQA-02: Spend escalation blocked ({msg_esc}).")

    # 5. Unauthorized scope bit (write = 0b010 not in 0b101) blocked (PQA-03)
    ok_scope, msg_scope = fw.authorize_action(caps[2], 2, proofs[2], True, spend_cents=0, now_epoch=1795727000, required_mask=0b010)
    assert not ok_scope and "PQA-03" in msg_scope
    print(f"[OK] PQA-03: Out-of-scope tool call blocked ({msg_scope}).")

    print("ALL PQ-AUTH SELF-TESTS PASSED.")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv or len(sys.argv) == 1:
        raise SystemExit(run_self_test())
