#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# inventory_gate.sh — diff an observed environment inventory against the
# pinned allowlist. PORTED VERBATIM from ltl-accumulator-verified apart from
# the axiom-surface assertion, which is repo-specific: there the corpus admits
# exactly one sanctioned axiom, here it admits none.
#
# This is THE production coverage gate: check.sh Phase 2c calls it, and the
# self-test exercises this exact script — the tested logic IS the shipping
# logic.
#
# Usage: inventory_gate.sh <observed-lean-output> <allowlist-file>
#
# Fail-closed in BOTH directions:
#   UNCLASSIFIED — constant in the environment, absent from the allowlist
#                  (new/renamed decl, changed kind, or changed axiom cone)
#   STALE        — allowlist entry absent from the environment
# plus an output-integrity check: the INV-COUNT trailer emitted by
# Proofs/Inventory.lean must equal the number of INV lines actually seen,
# so a truncated or crashed run can never pass as an empty diff.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
export LC_ALL=C   # byte-order collation: sort/comm must agree with Lean's String order
obs_file="$1"; allow_file="$2"

OBS=$(grep '^INV|' "$obs_file" | sort -u)
N_OBS=$(printf '%s' "$OBS" | grep -c '^INV|' || true)
TRAILER=$(grep '^INV-COUNT|' "$obs_file" | tail -1 | cut -d'|' -f2)
if [ -z "$TRAILER" ] || [ "$TRAILER" != "$N_OBS" ]; then
  echo "  INVENTORY TRUNCATED: trailer=${TRAILER:-absent}, observed $N_OBS lines"
  exit 1
fi

ALLOW=$(grep '^INV|' "$allow_file" | sort -u)
FAILGATE=0
UNCLASS=$(comm -23 <(printf '%s\n' "$OBS") <(printf '%s\n' "$ALLOW"))
STALE=$(comm -13 <(printf '%s\n' "$OBS") <(printf '%s\n' "$ALLOW"))
if [ -n "$UNCLASS" ]; then
  printf '%s\n' "$UNCLASS" | sed 's/^/  UNCLASSIFIED (in environment, not allowlisted): /'
  FAILGATE=1
fi
if [ -n "$STALE" ]; then
  printf '%s\n' "$STALE" | sed 's/^/  STALE (allowlisted, not in environment): /'
  FAILGATE=1
fi

# The audited corpus admits NO axiom declarations at all: the sanctioned
# external models live in gen/, outside every module these drivers cover, and
# are byte-pinned by Phase 0b. An axiom appearing here would be a declaration
# smuggled into the proof corpus, which Phase 2b also catches kernel-side —
# two independent gates on the same property, deliberately.
AXLINES=$(printf '%s\n' "$OBS" | grep '|axiom|' || true)
if [ -n "$AXLINES" ]; then
  echo "  AXIOM SURFACE DRIFT: the audited corpus must declare no axioms; observed:"
  printf '%s\n' "$AXLINES" | sed 's/^/    /'
  FAILGATE=1
fi

# The message must describe what was actually checked. It said "single
# sanctioned axiom" when ported, which is the accumulator's policy; here the
# audited corpus permits NONE, and a success line describing a different rule
# is how an assertion quietly stops meaning anything.
[ "$FAILGATE" = 0 ] && echo "  inventory gate: $N_OBS constants, environment == allowlist, zero axioms declared in the audited corpus"
exit "$FAILGATE"
