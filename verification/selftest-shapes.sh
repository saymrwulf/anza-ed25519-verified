#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# selftest-shapes.sh — can a declaration HIDE from the inventory walker?
#
# check.sh Phase 2c exists because a source-regex enumerator turned out to be
# evadable: in ltl-accumulator-verified a nine-attack self-test defeated one
# with attributed, private, indented and `instance` declarations and with a
# nested-namespace basename collision. The fix was to stop reading source text
# and ask the Lean environment instead, and that fix was PORTED here — see the
# note at the head of Phase 2c.
#
# But a fix ported is not a fix tested. `selftest-inventory.sh` proves the GATE
# reacts correctly to a difference; it feeds the gate synthetic observations and
# never runs the walker. Nothing in these four forks has ever asked the question
# the accumulator's suite asks: does the WALKER SEE a declaration written in an
# evasive shape? If it silently skipped one, the observation would match the
# allowlist, the gate would be satisfied, and a hidden theorem would ride along
# inside an audited module with every button green.
#
#   0  control: the untouched tree's observation equals the allowlist
#   1  FOUR EVASIVE SHAPES added to an audited module at once:
#        @[simp] theorem   an attribute in front of the declaration
#        private theorem   not exported, name mangled by the elaborator
#        instance          a declaration with no `theorem`/`def` keyword
#        nested namespace  Ns.Hidden.X, reusing the basename of an audited
#                          declaration Ns.X — the spelling-vs-membership shape.
#                          The victim module, its namespace and X are all
#                          derived from this repo's own manifest below.
#      EVERY ONE must be named in the gate's UNCLASSIFIED list. Asserting the
#      gate merely failed is not enough: one shape surfacing would fail the run
#      while the other three rode along unseen.
#
# One recompile of one leaf module, then the real Phase 2c. Run after a green
# check.sh.
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

# Pick the victim from this repo's own manifest rather than naming a module:
# the four forks do not share a corpus (dalek and anza carry Proofs.Basic;
# risc0 and betrusted do not), and a hard-coded name would silently pick
# nothing on half of them.
#
# The victim must be (a) in check.sh's PROOFS — attacking an unmanifested module
# would test the dead-file gate instead of the walker; (b) NOT an inventory
# driver or the audit driver — those are the instruments, and mutating one would
# be attacking the measuring device; (c) imported by no other manifest module,
# so one recompile cannot invalidate a second module's artifact. Of those, take
# the smallest, because this test compiles it twice.
#
# Note for anyone re-deriving this: the inventory drivers import the whole
# corpus, so they must be excluded from the set of importers as well as from the
# candidates. Leave them in and every module looks imported, no leaf is found,
# and the test silently has no victim at all.
MAIN=$(sed -n '/^PROOFS=(/,/^)/p' "$HERE/check.sh" \
       | sed 's/#.*//; s/PROOFS=(//; s/)//' | tr -s ' \t' '\n' | sed '/^$/d')
SEARCHERS=$(for m in $MAIN; do case $m in Inventory*|Audit) ;; *) echo "$HERE/Proofs/$m.lean";; esac; done)
VICTIM_MOD=""; _best=999999
for m in $MAIN; do
  case $m in Inventory*|Audit) continue;; esac
  grep -q "^import Proofs\.$m\$" $SEARCHERS 2>/dev/null && continue
  n=$(wc -l < "$HERE/Proofs/$m.lean")
  if [ "$n" -lt "$_best" ]; then _best=$n; VICTIM_MOD=$m; fi
done
if [ -z "$VICTIM_MOD" ]; then
  echo "FATAL: no manifested leaf module to attack — the corpus shape changed."; exit 1
fi
VICTIM_NS=$(grep -m1 '^namespace ' "$HERE/Proofs/$VICTIM_MOD.lean" | awk '{print $2}')
COLLIDE=$(grep -m1 '^theorem ' "$HERE/Proofs/$VICTIM_MOD.lean" | awk '{print $2}')
if [ -z "$VICTIM_NS" ] || [ -z "$COLLIDE" ]; then
  echo "FATAL: $VICTIM_MOD has no namespace or no theorem to collide with."; exit 1
fi

cleanup() {
  [ -f "$STASH/victim" ] && cp "$STASH/victim" "$HERE/Proofs/$VICTIM_MOD.lean"
  [ "$SAFE_EXIT" -eq 1 ] || rm -f "$HERE/Proofs/$VICTIM_MOD.olean" "$HERE/Proofs/$VICTIM_MOD.ilean"
  rm -rf "$STASH"
}
trap cleanup EXIT INT TERM
cp "$HERE/Proofs/$VICTIM_MOD.lean" "$STASH/victim"

# Phase 2c lifted from the shipping button. `set -euo pipefail` is copied from
# check.sh:32 deliberately — the phase does its Lean work in subshells, and
# without -e a failing subshell is masked by the next echo. (That exact mistake
# produced a green report for a red condition while selftest-tiers.sh was being
# built; do not "simplify" it away.)
lift() {
  # THE LIFT RANGE STOPS AT THE ACCOUNTING IDENTITY, and that boundary is the
  # fix for round-7 finding F5 (Claude). Phase 2c grew an accounting block that
  # reads $KERNLOG — a file created in Phase 2b, one phase ABOVE the lift. Under
  # `set -u` the driver aborted on its first expansion, so this self-test could
  # not pass on any fork from the moment that block was added. It failed loudly
  # rather than passing vacuously, which is why it was a red test and not a
  # false green; but it meant the four-shapes property went unverified.
  #
  # This test attacks the WALKER — can a declaration hide from the inventory —
  # and the accounting identity is a separate property with its own coverage.
  # Lifting it here would only drag in Phase 2b's state.
  awk '/^# ── Phase 2c/{f=1} f&&/^# ── (Phase 2c-accounting|Phase 3|Phases end)/{exit} f{print}' \
    "$HERE/check.sh" > "$STASH/payload.sh"

  { echo 'set -euo pipefail'
    echo 'source ~/aeneas-toolchain/env.sh'
    echo "HERE=\"$HERE\""
    echo 'AENEAS_LEAN="$AENEAS_HOME/backends/lean"'
    echo "TIMEOUT=$TIMEOUT"
    # PROOFS, and the scalar manifest the coverage check consults. Both are
    # lifted VERBATIM rather than re-derived here: re-deriving would let this
    # test's idea of the manifest drift away from the button's, and then the
    # test would be checking its own opinion instead of the shipping one.
    sed -n '/^PROOFS=(/,/^)/p;/^SCALAR_SH=/p;/^SCALAR_MANIFEST=/p' "$HERE/check.sh"
    cat "$STASH/payload.sh"
  } > "$STASH/p2c.sh"

  # Guard on the PAYLOAD, not the concatenation. The previous version grepped
  # the assembled file, so a marker appearing in the preamble or in a lifted
  # definition would have satisfied it — the same shape as the line-count check
  # that an empty driver once passed because the CERTS array padded it.
  for want in 'Phase 2c' 'inventory_gate.sh'; do
    grep -qF "$want" "$STASH/payload.sh" || {
      echo "FATAL: the lifted PAYLOAD has no '$want' — check.sh's phase markers moved."; exit 1; }
  done
  for want in 'PROOFS=(' 'SCALAR_MANIFEST='; do
    grep -qF "$want" "$STASH/p2c.sh" || {
      echo "FATAL: the lift carries no '$want' — a definition the phase needs is missing."; exit 1; }
  done

  # AND THE DURABLE GUARD: every variable the payload READS must be one the
  # driver DEFINES. Derived mechanically rather than from a hand-kept list,
  # because a hand-kept list is exactly what failed — the phase grew a
  # dependency nobody thought to add. Shared with the other four lifting
  # self-tests: ONE implementation, pinned, rather than five copies of the
  # thing whose whole failure mode is drifting out of sync.
  "$HERE/lift-guard.sh" "$STASH/payload.sh" "$STASH/p2c.sh" "check.sh Phase 2c" || exit 1
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

run_phase() { bash "$STASH/p2c.sh" 2>&1; }

echo "=== selftest-shapes: can a declaration hide from the walker? ==="
echo "    victim: Proofs/$VICTIM_MOD.lean ($_best lines), namespace $VICTIM_NS"
echo "    colliding basename: $VICTIM_NS.$COLLIDE"

if ! recompile; then
  echo "FATAL: Proofs/$VICTIM_MOD.lean does not compile before any attack — fix the tree first."
  exit 1
fi

# ── 0. control ─────────────────────────────────────────────────────────────
OUT=$(run_phase); RC=$?
if [ "$RC" -eq 0 ] && grep -qF "environment == allowlist" <<<"$OUT"; then
  echo "  ✓ control: the untouched tree's observation equals the allowlist"
else
  echo "  ✗ control: exit $RC — the tree is not green before the attack"
  tail -8 <<<"$OUT" | sed 's/^/      /'
  FAILURES=$((FAILURES+1))
fi

# ── 1. the four shapes ─────────────────────────────────────────────────────
python3 - "$HERE/Proofs/$VICTIM_MOD.lean" "$VICTIM_NS" "$COLLIDE" <<'PY'
import sys
f, ns, collide = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(f).read()
end = f"\nend {ns}"
assert s.rstrip().endswith(end.strip()), "victim does not end by closing its namespace"
i = s.rstrip().rfind(end)
inject = f"""
-- selftest-shapes: four declaration shapes that defeated a source-regex
-- enumerator in ltl-accumulator-verified. Each must surface in the walker's
-- observation. Removed by this script's cleanup.
@[simp] theorem shape_attributed : True := trivial

private theorem shape_private : True := trivial

instance shape_instance : Nonempty Nat := ⟨0⟩

namespace Hidden
theorem {collide} : True := trivial
end Hidden
"""
open(f, "w").write(s[:i] + inject + s[i:])
PY

if ! recompile; then
  echo "  ✗ case 1: the module with the four shapes did not compile (case is vacuous)"
  FAILURES=$((FAILURES+1))
else
  OUT=$(run_phase); RC=$?
  if [ "$RC" -eq 0 ]; then
    echo "  ✗ case 1: FOUR hidden declarations and the inventory passed — the walker is blind"
    FAILURES=$((FAILURES+1))
  else
    # Not "did it fail" but "did it see each one". A gate that reports three of
    # four still lets one declaration ride along inside an audited module.
    MISSED=0
    for n in "$VICTIM_NS.shape_attributed" "shape_private" \
             "$VICTIM_NS.shape_instance"   "$VICTIM_NS.Hidden.$COLLIDE"; do
      if grep -qF "UNCLASSIFIED" <<<"$OUT" && grep -F "UNCLASSIFIED" <<<"$OUT" | grep -qF "$n"; then
        echo "      · seen: $n"
      else
        echo "      · NOT SEEN: $n — this shape hides from the walker"
        MISSED=1
      fi
    done
    if [ "$MISSED" -eq 0 ]; then
      echo "  ✓ case 1: all four evasive shapes surfaced as UNCLASSIFIED"
    else
      echo "  ✗ case 1: the gate failed, but not for every shape"
      grep -F "UNCLASSIFIED" <<<"$OUT" | head -8 | sed 's/^/        /'
      FAILURES=$((FAILURES+1))
    fi
  fi
fi

cp "$STASH/victim" "$HERE/Proofs/$VICTIM_MOD.lean"
if recompile; then
  SAFE_EXIT=1
else
  echo "  ✗ restore: the ORIGINAL module no longer compiles — tree left for inspection"
  FAILURES=$((FAILURES+1))
fi

OUT=$(run_phase); RC=$?
if [ "$RC" -eq 0 ] && grep -qF "environment == allowlist" <<<"$OUT"; then
  echo "  ✓ restored: the observation equals the allowlist again"
else
  echo "  ✗ restored: the tree did not come back green (exit $RC)"
  FAILURES=$((FAILURES+1))
fi

echo ""
if [ "$FAILURES" -eq 0 ]; then
  echo "SELFTEST PASSED — no declaration shape tested here can hide inside an"
  echo "audited module: the walker reports each one by name."
  exit 0
fi
echo "SELFTEST FAILED: $FAILURES case(s) did not behave as claimed."
exit 1
