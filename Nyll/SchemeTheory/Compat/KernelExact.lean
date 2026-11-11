/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Environment
public meta import Lean.MetavarContext
public meta import Lean.Meta.Basic
public meta import Lean.Meta.ExprDefEq

/-!
# Kernel-checked exact proof elaboration

A resolved proof can have a type whose elaborator comparison is expensive even though the kernel
checks the same conversion directly. The project-specific tactic below elaborates the original
proof without an expected type, requires complete resolution, and validates its type with the
kernel before using the usual checked goal assignment. Normal declaration kernel checking remains
unchanged.
-/

public meta section

namespace Nyll.SchemeTheory.Compat

/-- Close the main goal with a fully resolved proof after direct kernel validation.

The syntax is nyll_kernel_exact term. The original term is elaborated without an expected type
and with recovery disabled. All expression and universe metavariables in the proof, target and
local context must resolve. The kernel must accept the proof and identify its inferred type with
the original goal before the ordinary scope/occurs checked assignment runs. Other goals are
preserved, and normal declaration kernel checking remains enabled. -/
elab (name := nyllKernelExact) "nyll_kernel_exact " proof:term : tactic =>
  Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let rawProof ← Lean.Elab.Tactic.elabTerm proof none (mayPostpone := false)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let value ← Lean.instantiateMVars rawProof
    let target ← Lean.instantiateMVars (← goal.getType)
    let lctx ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
    if value.hasMVar || target.hasMVar then
      throwError "nyll_kernel_exact refuses unresolved expression or universe metavariables"
    for d in lctx do
      let unresolvedValue := match d.value? true with
        | none => false
        | some body => body.hasMVar
      if d.type.hasMVar || unresolvedValue then
        throwError "nyll_kernel_exact refuses unresolved metavariables in the local context"
    let env ← Lean.getEnv
    let actualType ← match Lean.Kernel.check env lctx value with
      | .ok type => pure type
      | .error _ => throwError "nyll_kernel_exact: Kernel.check rejected the original proof"
    let actualType ← Lean.instantiateMVars actualType
    if actualType.hasMVar then
      throwError "nyll_kernel_exact refuses an unresolved kernel-inferred proof type"
    match Lean.Kernel.isDefEq env lctx actualType target with
    | .ok true => pure ()
    | .ok false => throwError "nyll_kernel_exact: kernel proof type does not match the goal"
    | .error _ => throwError "nyll_kernel_exact: kernel comparison failed"
    if (← goal.isAssigned) then
      throwError "nyll_kernel_exact: main goal was assigned unexpectedly"
    unless (← Lean.Elab.Tactic.getMainGoal) == goal do
      throwError "nyll_kernel_exact: main goal changed during proof checking"
    unless (← goal.checkedAssign value) do
      throwError "nyll_kernel_exact: ordinary scope/occurs assignment checks rejected the proof"
    unless (← goal.isAssigned) do
      throwError "nyll_kernel_exact: checked assignment did not close the goal"
    Lean.Elab.Tactic.replaceMainGoal []

end Nyll.SchemeTheory.Compat
