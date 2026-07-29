#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-inventory.sh — adversarial self-test for check.sh Phase 2c.
#
# WHAT PHASE 2c IS FOR. Phase 2b asks the kernel whether any AXIOM is declared
# under Proofs/. It says nothing about the ~3000 other declarations. Phase 3
# pins the cones of the 31 named certificates. Between them sits everything
# else: a helper lemma that quietly acquired an oracle in its cone, a
# declaration added, removed or renamed, a compiler-generated auxiliary that
# changed shape. Phase 2c pins that whole surface and diffs it both ways.
#
# Cases, each asserting a SPECIFIC diagnostic:
#   0  positive control: the untouched tree passes
#   1  an allowlist row deleted        -> UNCLASSIFIED (in env, not allowlisted)
#   2  an allowlist row invented       -> STALE (allowlisted, not in env)
#   3  a cone silently widened         -> BOTH, because the record changed
#   4  an axiom row appears            -> AXIOM SURFACE DRIFT
#   5  the count trailer disagrees     -> INVENTORY TRUNCATED (no vacuous pass)
#
# It runs the SHIPPING inventory_gate.sh against a recorded observation, so no
# Lean is needed and the whole thing takes a second. The observation itself is
# produced by check.sh Phase 2c; this test attacks the gate that judges it.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
FAILURES=0
STASH="$(mktemp -d)"
trap 'rm -rf "$STASH"' EXIT INT TERM

ALLOW="$HERE/inventory-allowlist.txt"
[ -s "$ALLOW" ] || { echo "FATAL: inventory-allowlist.txt missing or empty"; exit 1; }

# The observation a green run would produce: the allowlist itself plus a
# trailer. Deriving it from the allowlist is exactly right for this test — the
# question is whether the GATE reacts correctly to differences, and each case
# below introduces one.
mkobs() {  # mkobs <file> [extra-line...]
  local out="$1"; shift
  grep '^INV|' "$ALLOW" > "$out"
  for l in "$@"; do printf '%s\n' "$l" >> "$out"; done
  LC_ALL=C sort -o "$out" "$out"
  echo "INV-COUNT|$(grep -c '^INV|' "$out")" >> "$out"
}

expect() {  # expect <label> <obs> <allow> <want-rc> <want-substring>
  local label="$1" obs="$2" allow="$3" want_rc="$4" want_txt="$5" out rc
  out=$("$HERE/inventory_gate.sh" "$obs" "$allow" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  ✗ $label: exit $rc, expected $want_rc"; echo "$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  ✗ $label: exit code right, diagnostic wrong (rejected for the wrong reason)"
    echo "      wanted: $want_txt"; echo "$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ✓ $label"
}

echo "=== selftest-inventory: attacking check.sh Phase 2c's gate ==="

# ── 0. positive control ────────────────────────────────────────────────────
mkobs "$STASH/obs.txt"
expect "case 0 control: a faithful observation passes" "$STASH/obs.txt" "$ALLOW" 0 "environment == allowlist"

# ── 1. a row deleted from the allowlist: the declaration is still there, so
#      the gate must report it as unclassified rather than shrug.
VICTIM=$(grep '^INV|' "$ALLOW" | grep '|theorem|' | head -1)
grep -vxF "$VICTIM" "$ALLOW" > "$STASH/allow-short.txt"
expect "case 1: allowlist row deleted -> UNCLASSIFIED" "$STASH/obs.txt" "$STASH/allow-short.txt" 1 "UNCLASSIFIED"

# ── 2. a row invented in the allowlist: nothing in the environment matches it.
cp "$ALLOW" "$STASH/allow-extra.txt"
echo "INV|Proofs.Ghost|CurveFieldProofs.ghost_lemma|theorem|Classical.choice" >> "$STASH/allow-extra.txt"
expect "case 2: allowlist row with no declaration -> STALE" "$STASH/obs.txt" "$STASH/allow-extra.txt" 1 "STALE"

# ── 3. THE ONE THAT MATTERS: a cone silently widened. Same module, same name,
#      same kind — only the axiom cone grew. Phases 2b and 3 both pass this:
#      2b only looks for axiom DECLARATIONS, and 3 only pins the 31 named
#      certificates. If the victim is not one of those, nothing else sees it.
WIDENED=$(sed 's/$/,sha2.Sha512/' <<<"$VICTIM")
mkobs "$STASH/obs-wide.txt"
grep -vxF "$VICTIM" "$STASH/obs-wide.txt" > "$STASH/t" && mv "$STASH/t" "$STASH/obs-wide.txt"
printf '%s\n' "$WIDENED" >> "$STASH/obs-wide.txt"
LC_ALL=C sort -o "$STASH/obs-wide.txt" "$STASH/obs-wide.txt"
echo "INV-COUNT|$(grep -c '^INV|' "$STASH/obs-wide.txt")" >> "$STASH/obs-wide.txt"
expect "case 3: a cone widened by one oracle -> UNCLASSIFIED" "$STASH/obs-wide.txt" "$ALLOW" 1 "UNCLASSIFIED"

# ── 4. an axiom appears in the audited corpus. The sanctioned external models
#      live in gen/, outside every module the drivers cover, so any axiom here
#      is a declaration smuggled into the proof corpus.
mkobs "$STASH/obs-ax.txt" "INV|Proofs.FeQ|CurveFieldProofs.rogue|axiom|"
expect "case 4: an axiom in the corpus -> AXIOM SURFACE DRIFT" "$STASH/obs-ax.txt" "$ALLOW" 1 "AXIOM SURFACE DRIFT"

# ── 5. truncation. "Nothing found" and "nothing wrong" must not share a path:
#      a crashed or cut-short run has to fail, not pass as an empty diff.
grep '^INV|' "$ALLOW" | head -100 > "$STASH/obs-trunc.txt"
echo "INV-COUNT|$(grep -c '^INV|' "$ALLOW")" >> "$STASH/obs-trunc.txt"
expect "case 5: trailer disagrees with the lines -> INVENTORY TRUNCATED" "$STASH/obs-trunc.txt" "$ALLOW" 1 "INVENTORY TRUNCATED"

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — Phase 2c's gate rejects surface drift in both directions,"
  echo "for the stated reason in each case."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES case(s) did not behave as claimed."
exit 1
