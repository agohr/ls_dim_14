import QuaternionicSymmetry
import Lean.Util.CollectAxioms

/-! Check the transitive axiom dependencies of every project declaration.

The three allowed axioms are Lean's usual logical foundations. In particular,
`sorryAx`, `Lean.ofReduceBool`, and any custom mathematical axiom are rejected.
This verifies proof integrity, not completeness of the intended mathematics.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    if (`QuaternionicSymmetry).isPrefixOf name then some name else none
  if names.isEmpty then
    throwError "No project declarations found; an empty library is not an audit pass."
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  -- Share the visited set across roots: common mathlib dependencies need checking once.
  let mut state : CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((CollectAxioms.collect name).run env).run state
    let forbidden := next.axioms.filter fun ax => !allowed.contains ax
    unless forbidden.isEmpty do
      throwError "{name} depends on forbidden axioms: {forbidden}"
    state := next
  logInfo m!"Audited {names.length} project declarations: only propext, Classical.choice, Quot.sound permitted."
