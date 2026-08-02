#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-tiers.sh — adversarial self-test for the TWO-TIER axiom boundary.
#
# This repository has two tiers and the distinction is the most valuable
# property it has:
#
#   · the ARITHMETIC tier — field, curve, scalar and encoding certificates —
#     must rest on Lean's three kernel axioms and NOTHING else. No hash oracle,
#     no wire-format opacity. That is what makes "the curve arithmetic is
#     proven" a claim about mathematics rather than about assumptions;
#   · the APEX tier — the four signature certificates — legitimately carries
#     this fork's SHA-512 and wire-format axioms, because a signature scheme
#     cannot be verified without a hash.
#
# Collapsing the two, by widening the arithmetic tier to accept oracles, would
# destroy that property while every button stayed green — and it is exactly
# what a single careless edit to a shared lemma does. Until 2026-07-30 nothing
# tested it. These cases do.
#
#   0  control: untouched tree passes
#   1  AN APEX ORACLE LEAKED INTO AN ARITHMETIC CERTIFICATE. A hash axiom is
#      introduced into the proof of an arithmetic certificate — statement
#      unchanged, so only the cone moves. Phase 3 must name that certificate.
#   2  the apex boundary WIDENED by one name -> apex cones no longer match
#   3  the apex boundary NARROWED by one name -> same, from the other side
#
# Case 1 recompiles one module and is the slow one (~2 min). Cases 2 and 3 need
# no Lean at all. Run after a green check.sh.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
TIMEOUT="${LEAN_TIMEOUT:-900}"
export LEAN_MEM_MB="${LEAN_MEM_MB:-8192}"
FAILURES=0
SAFE_EXIT=0
STASH="$(mktemp -d)"

# The audit phases write a temporary driver (.audit-XXXX.lean / .apex-XXXX.lean)
# and delete it on the way out — but a phase that exits 1 never reaches its own
# rm. This test provokes four such exits on purpose, so it is this test's job to
# clear the residue. Record what was here first and remove only what we caused;
# litter that predates the run is somebody else's finding, not ours to hide.
shopt -s nullglob
LITTER_BEFORE="$(printf '%s\n' "$HERE"/.audit-*.lean "$HERE"/.apex-*.lean | sort)"
shopt -u nullglob

VICTIM_MOD=PointEqSpec
VICTIM_CERT=CurveFieldProofs.enc_point_inj

# Which apex axiom to smuggle downward is a per-fork question, so derive it
# rather than hard-code it: take this repo's own documented apex boundary, drop
# the three kernel axioms, and keep the names that are actually declared inside
# the victim module's import closure — an axiom the victim cannot see cannot be
# injected into it. Prefer a hash oracle when one is reachable (dalek reaches
# verifying.sha512_new); the three forks that route SHA-512 through a single
# apex-only module reach only the wire-format axioms, which serve equally well:
# the property under test is that NO apex axiom may appear in this tier.
import_closure() {  # every .lean file the victim module transitively imports
  local -A seen=(); local -a q=("$VICTIM_MOD"); local m f i
  while [ ${#q[@]} -gt 0 ]; do
    m="${q[0]}"; q=("${q[@]:1}")
    [ -n "${seen[$m]:-}" ] && continue
    seen[$m]=1
    for f in "$HERE/Proofs/$m.lean" "$HERE/gen/${m//.//}.lean"; do
      [ -f "$f" ] || continue
      echo "$f"
      while read -r i; do q+=("$i"); done \
        < <(grep '^import ' "$f" | awk '{print $2}' | sed 's/^Proofs\.//')
    done
  done
}
oracle_for_this_fork() {
  local allowed closure m
  allowed=$(grep -h "ALLOWED='" "$HERE/check.sh" | sed "s/.*ALLOWED='\[//;s/\].*//" \
            | tr ',' '\n' | sed 's/^ *//;s/ *$//' \
            | grep -v '^propext$\|^Classical.choice$\|^Quot.sound$')
  closure=$(import_closure)
  for m in $(echo "$allowed" | grep 'sha512\|sha2') $allowed; do
    if grep -qE "^axiom ${m//./\\.}( |:)" $closure 2>/dev/null; then echo "$m"; return; fi
  done
}
ORACLE="$(oracle_for_this_fork)"
if [ -z "$ORACLE" ]; then
  echo "FATAL: this fork's apex boundary lists no axiom this test can inject."; exit 1
fi

cleanup() {
  [ -f "$STASH/victim" ] && cp "$STASH/victim" "$HERE/Proofs/$VICTIM_MOD.lean"
  [ -f "$STASH/check"  ] && cp "$STASH/check"  "$HERE/check.sh"
  [ -f "$STASH/pins"   ] && cp "$STASH/pins"   "$HERE/HARNESS.sha256"
  # If we are dying mid-case the victim's .olean may still hold the injected
  # oracle while its source no longer shows it. That artifact is worse than no
  # artifact: it is a poisoned object with a clean source. Remove it. Phase 3's
  # vacuous-scan guard then fails loudly, and any full run rebuilds it anyway.
  # On the normal path the run has already restored and rebuilt the module, so
  # deleting it there would leave the tree worse than we found it — an
  # --audit-only run afterwards would fail on a missing artifact we removed.
  [ "$SAFE_EXIT" -eq 1 ] || rm -f "$HERE/Proofs/$VICTIM_MOD.olean" "$HERE/Proofs/$VICTIM_MOD.ilean"
  local f
  shopt -s nullglob
  for f in "$HERE"/.audit-*.lean "$HERE"/.apex-*.lean; do
    grep -qxF "$f" <<<"$LITTER_BEFORE" || rm -f "$f" "${f%.lean}.olean"
  done
  shopt -u nullglob
  rm -rf "$STASH"
}
trap cleanup EXIT INT TERM
cp "$HERE/Proofs/$VICTIM_MOD.lean" "$STASH/victim"
cp "$HERE/check.sh"                "$STASH/check"
cp "$HERE/HARNESS.sha256"          "$STASH/pins"

# The axiom audit, lifted from the shipping button so the tested logic is the
# shipping logic. BOTH tiers live under the one "Phase 3" marker — the
# per-certificate arithmetic audit and, below it, the apex boundary check. An
# earlier draft of this file lifted them as two markers, got an empty driver for
# the second, and the driver still cleared a line-count sanity check because the
# CERTS array padded it. So the guard below looks for the two diagnostics we
# intend to provoke, not for a number of lines.
lift() {
  # set -euo pipefail, verbatim from the button. The -e is load-bearing and was
  # missing from an earlier draft: the phase's Lean work happens in a subshell
  # and the phase ends with a bare `echo ""`, so without -e a subshell that
  # exits 1 is masked by the echo's success and the driver reports green while
  # printing APEX AUDIT FAILED. The button gets this right at check.sh:32; a
  # lift that does not copy it tests something the button never runs.
  awk '/^# ── Phase 3: axiom audit/{f=1} f&&/^# ── (Phase 3c|Phases end)/{exit} f{print}' \
    "$HERE/check.sh" > "$STASH/payload.sh"
  { echo 'set -euo pipefail'
    echo 'source ~/aeneas-toolchain/env.sh'
    echo "HERE=\"$HERE\""
    echo 'AENEAS_LEAN="$AENEAS_HOME/backends/lean"'
    echo "TIMEOUT=$TIMEOUT"
    sed -n '/^EXPECTED=/p;/^AUDIT_IMPORTS=(/,/^)/p;/^CERTS=(/,/^)/p' "$HERE/check.sh"
    cat "$STASH/payload.sh"
  } > "$STASH/p3.sh"
  # The two diagnostics must come from the PAYLOAD; the three definitions are
  # preamble, so those are asserted on the assembled driver.
  for want in 'AXIOM AUDIT FAILED' 'APEX AUDIT FAILED'; do
    if ! grep -qF "$want" "$STASH/payload.sh"; then
      echo "FATAL: the lifted driver has no '$want' — check.sh's phase markers moved."
      exit 1
    fi
  done
  for want in 'CERTS=(' 'AUDIT_IMPORTS=(' 'EXPECTED='; do
    if ! grep -qF "$want" "$STASH/p3.sh"; then
      echo "FATAL: the lift carries no '$want' — a definition the phase needs is missing."
      exit 1
    fi
  done
  "$HERE/lift-guard.sh" "$STASH/payload.sh" "$STASH/p3.sh" "check.sh Phase 3" || exit 1
}
lift

recompile() {
  ( cd "$AENEAS_LEAN" && lake env bash -c "
      set -uo pipefail
      cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
      cd '$HERE'
      LEAN_TIMEOUT=$TIMEOUT '$HERE/lean-guard' Proofs/$VICTIM_MOD.lean
  " ) >/dev/null 2>&1
}

expect() {  # expect <driver> <label> <want-rc> <want-substring>
  local drv="$1" label="$2" want_rc="$3" want_txt="$4" out rc
  out=$(bash "$STASH/$drv.sh" 2>&1); rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    echo "  ✗ $label: exit $rc, expected $want_rc"; tail -5 <<<"$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  if ! grep -qF "$want_txt" <<<"$out"; then
    echo "  ✗ $label: exit code right, diagnostic wrong (rejected for the wrong reason)"
    echo "      wanted: $want_txt"; tail -5 <<<"$out" | sed 's/^/      /'
    FAILURES=$((FAILURES+1)); return
  fi
  echo "  ✓ $label"
}

echo "=== selftest-tiers: attacking the arithmetic/apex boundary ==="
echo "    victim: $VICTIM_CERT in Proofs/$VICTIM_MOD.lean"
echo "    oracle: $ORACLE (from this repo's own apex boundary)"

# Prime the victim. This test rebuilds that one module twice, and its cleanup
# deliberately deletes the .olean if it dies mid-case — so on entry the artifact
# may be missing or stale from an interrupted earlier run. Rebuilding it here
# means a red control is a real red, not leftovers.
if ! recompile; then
  echo "FATAL: Proofs/$VICTIM_MOD.lean does not compile before any attack — fix the tree first."
  exit 1
fi

expect p3 "control: both tiers pass" 0 "no curve/scalar/backend axioms"

# ── 1. THE ONE THAT MATTERS ────────────────────────────────────────────────
# Introduce a hash oracle into an arithmetic certificate's PROOF. The statement
# does not change, so the statement digest would not move; only the cone does.
# The arithmetic tier's whole claim is that this cannot happen unnoticed.
python3 - "$HERE/Proofs/$VICTIM_MOD.lean" "$VICTIM_CERT" "$ORACLE" <<'PY'
import sys, re
f, cert, oracle = sys.argv[1], sys.argv[2], sys.argv[3]
short = cert.split('.')[-1]
s = open(f).read()
m = re.search(r'^(theorem %s\b.*?:=\s*by\b)' % re.escape(short), s, re.M | re.S)
assert m, f"could not find a tactic proof for {short}"
inject = m.group(1) + f"\n  have _oracle_leak := {oracle}"
open(f, "w").write(s[:m.start(1)] + inject + s[m.end(1):])
PY
if recompile; then
  expect p3 "case 1: an apex oracle in an arithmetic certificate" 1 "AXIOM AUDIT FAILED"
else
  echo "  ✗ case 1: the injected module did not compile (case is vacuous)"
  FAILURES=$((FAILURES+1))
fi
cp "$STASH/victim" "$HERE/Proofs/$VICTIM_MOD.lean"
if recompile; then
  SAFE_EXIT=1   # victim is back to its committed source and rebuilt from it
else
  echo "  ✗ restore: the ORIGINAL module no longer compiles — tree left for inspection"
  FAILURES=$((FAILURES+1))
fi

# ── 2/3. the apex boundary moved, either way ───────────────────────────────
# Phase 3b requires the apex cones to equal the documented boundary EXACTLY.
# Widening it is how an oracle would be smuggled in; narrowing it is how a
# real dependency would be hidden. Both must fail.
sed -i "s/ALLOWED='\[propext, /ALLOWED='[propext, Classical.byContradiction, /" "$HERE/check.sh"
lift
expect p3 "case 2: apex boundary widened by one name" 1 "APEX AUDIT FAILED"
cp "$STASH/check" "$HERE/check.sh"

sed -i "s/ALLOWED='\[propext, Classical.choice, /ALLOWED='[propext, /" "$HERE/check.sh"
lift
expect p3 "case 3: apex boundary narrowed by one name" 1 "APEX AUDIT FAILED"
cp "$STASH/check" "$HERE/check.sh"
lift

expect p3 "restored: both tiers pass again" 0 "no curve/scalar/backend axioms"

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — the arithmetic tier cannot silently acquire an oracle,"
  echo "and the apex boundary cannot be moved in either direction."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES case(s) did not behave as claimed."
exit 1
