#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$repo_root"
probe_source=GonshorBirthday/AuditProbe.lean
for fixture in "$probe_source" ProbeChallenge.lean ProbeSolution.lean; do
  if [[ -e $fixture ]]; then
    echo "Refusing to overwrite existing audit fixture: $fixture" >&2
    exit 1
  fi
done
probe_dir=$(mktemp -d "${TMPDIR:-/tmp}/gonshor-birthday-audit.XXXXXX")
cleanup() {
  rm -f -- "$probe_source" ProbeChallenge.lean ProbeSolution.lean
  rm -f -- .lake/build/lib/lean/ProbeChallenge.* .lake/build/lib/lean/ProbeSolution.*
  rm -f -- .lake/build/lib/lean/GonshorBirthday/AuditProbe.*
  rm -f -- .lake/build/ir/ProbeChallenge.* .lake/build/ir/ProbeSolution.*
  rm -f -- .lake/build/ir/GonshorBirthday/AuditProbe.*
  rm -rf -- "$probe_dir"
}
trap cleanup EXIT
expect_rejection() {
  local label=$1 expected=$2
  shift 2
  if "$@" > "$probe_dir/output" 2>&1; then
    echo "audit-probes: $label incorrectly accepted the bad fixture" >&2
    exit 1
  fi
  if ! grep -Fq -- "$expected" "$probe_dir/output"; then
    cat "$probe_dir/output" >&2
    echo "audit-probes: $label failed for an unexpected reason" >&2
    exit 1
  fi
}

# The textual gate must reject drift instead of merely counting proof holes.
mkdir -p "$probe_dir/scripts" "$probe_dir/GonshorBirthday/Inline"
cp comparator.json Challenge.lean Solution.lean "$probe_dir/"
cp scripts/palomar-statement.txt "$probe_dir/scripts/"
cp GonshorBirthday/Inline/Basic.lean GonshorBirthday/Inline/Ordinal.lean \
  GonshorBirthday/Inline/Birthday.lean "$probe_dir/GonshorBirthday/Inline/"
printf '\n-- deliberate drift\n' >> "$probe_dir/Challenge.lean"
expect_rejection statement-drift 'has drifted' \
  scripts/check-palomar-challenge.sh --repo "$probe_dir"

# A fresh declared axiom is forbidden even if no theorem imports or uses it.
printf '%s\n' 'module' 'public section' '/-- Deliberately forbidden audit fixture. -/' 'axiom auditProbeForbidden : False' > "$probe_source"
lake build GonshorBirthday.AuditProbe
expect_rejection axiom 'forbidden axiom' lake exe axioms

# The sole advertised Challenge hole must not license holes in the proof library.
cat > "$probe_source" <<'LEAN'
module
public section
/-- warning: declaration uses `sorry` -/
#guard_msgs in
set_option warningAsError false in
/-- Deliberately admitted audit fixture. -/
theorem auditProbeSorry : False := by sorry
LEAN
lake build GonshorBirthday.AuditProbe
expect_rejection admitted-proof 'forbidden axiom sorryAx' lake exe axioms
rm -f -- "$probe_source"

# Module-private values reached through a public definition are still nonportable.
for fixture in ProbeChallenge ProbeSolution; do
  cat > "$fixture.lean" <<'LEAN'
module
private def hidden : Prop := True
/-- A public statement with a deliberately private transitive value. -/
public def auditPublicStatement : Prop := hidden
/-- Deliberately nonportable audit fixture. -/
public theorem auditPortability : auditPublicStatement := by
  rw [auditPublicStatement, hidden]
  exact True.intro
LEAN
  lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true \
    -o ".lake/build/lib/lean/$fixture.olean" "$fixture.lean"
done
expect_rejection private-statement 'module-private statement dependency' \
  lake exe palomar-compatibility ProbeChallenge ProbeSolution auditPortability

# Identical theorem type expressions must not hide differing public definition bodies.
cat > ProbeChallenge.lean <<'LEAN'
module
/-- An explicit local statement definition. -/
public def auditPublicStatement : Prop := True
/-- A fixture with a matching advertised type. -/
public theorem auditPortability : auditPublicStatement := True.intro
LEAN
cat > ProbeSolution.lean <<'LEAN'
module
/-- A deliberately changed local statement definition. -/
public def auditPublicStatement : Prop := True ∧ True
/-- A fixture whose type has the same constant name but a different meaning. -/
public theorem auditPortability : auditPublicStatement := ⟨True.intro, True.intro⟩
LEAN
for fixture in ProbeChallenge ProbeSolution; do
  lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true \
    -o ".lake/build/lib/lean/$fixture.olean" "$fixture.lean"
done
expect_rejection definition-drift 'statement declaration does not match' \
  lake exe palomar-compatibility ProbeChallenge ProbeSolution auditPortability

cleanup
trap - EXIT
# After removing fixtures, the real project must still pass both compiled gates.
lake exe palomar-compatibility
lake exe axioms
echo "audit-probes: all negative controls were rejected and fixture state was removed"
