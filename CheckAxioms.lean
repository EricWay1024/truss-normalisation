import Truss.Transfer
import Lean.Util.CollectAxioms

/-! Publication check: inspect the union of exported theorem dependencies once. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`Truss.Transfer).isPrefixOf name || name.toString.startsWith "_private.Truss.Transfer." then
      match info with
      | .thmInfo _ => some name
      | _ => none
    else none
  if names.isEmpty then throwError "No Transfer theorems found"
  -- Shared visited-set: calling collectAxioms separately would re-traverse Mathlib
  -- for every theorem. This uses the same kernel-environment dependency walker.
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Transfer theorem dependency contains unexpected axiom {ax}"
  logInfo m!"Checked {names.length} Transfer theorems; axioms: {state.axioms}"
