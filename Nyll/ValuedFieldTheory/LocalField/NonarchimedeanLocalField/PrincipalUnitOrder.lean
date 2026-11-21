/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Lean.Elab.Tactic.Omega
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.Ramification.Different.Powers

/-!
# Order detected by positive principal-unit levels

The units `1 + a`, with `a` in a positive maximal-ideal power, recover that
entire ideal power. Thus the actual unit filtration detects the reverse order
on positive depths, both in the integer ring and in the field.
-/

@[expose] public section

noncomputable section

universe u

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Containment of positive principal-unit groups detects the reverse depth order. -/
theorem principalUnits_le_iff {r s : ℕ} (hr : 1 ≤ r) :
    principalUnits K r ≤ principalUnits K s ↔ s ≤ r := by
  constructor
  · intro h
    apply (RamificationTheory.DiscreteValuationRing.maximalIdeal_pow_le_iff 𝒪[K] K r s).mp
    intro a ha
    have hu := h (principalUnitOneAddOfMemPowSubgroup K hr a ha).property
    change principalUnitOneAddOfMemPow K hr a ha ∈ principalUnits K s at hu
    rw [mem_principalUnits_iff, principalUnitOneAddOfMemPow_val,
      add_sub_cancel_left] at hu
    exact hu
  · exact principalUnits_antitone K

/-- The same order criterion for principal units inside the field multiplicative group. -/
theorem fieldPrincipalUnits_le_iff {r s : ℕ} (hr : 1 ≤ r) :
    fieldPrincipalUnits K r ≤ fieldPrincipalUnits K s ↔ s ≤ r := by
  constructor
  · intro h
    apply (principalUnits_le_iff K hr).mp
    intro a ha
    obtain ⟨b, hb, hba⟩ := h ⟨a, ha, rfl⟩
    have hba' : b = a := integerUnitsToFieldUnits_injective K hba
    exact hba' ▸ hb
  · intro h
    exact Subgroup.map_mono (principalUnits_antitone K h)

/-- Each positive principal-unit level strictly contains the next level. -/
theorem fieldPrincipalUnits_succ_lt {r : ℕ} (hr : 1 ≤ r) :
    fieldPrincipalUnits K (r + 1) < fieldPrincipalUnits K r := by
  apply lt_of_le_not_ge
  · exact (fieldPrincipalUnits_le_iff K (by omega)).mpr (Nat.le_succ r)
  · rw [fieldPrincipalUnits_le_iff K hr]
    omega

end LocalFieldTheory
