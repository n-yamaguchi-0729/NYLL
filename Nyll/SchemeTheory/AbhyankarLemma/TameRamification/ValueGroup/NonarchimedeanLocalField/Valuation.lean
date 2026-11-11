/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation
public import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.FieldNorm.Image
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic

/-!
# Neu1999 local-field valuations

This file packages the normalized integer valuation from
`IsNonarchimedeanLocalField` as the `MultiplicativeIntegerValuation` used by
the tame Abhyankar value-group layer, and rewrites the Neu1999 norm formula
for the field-norm API.
-/

@[expose] public section

noncomputable section

universe u

namespace TameAbhyankar

open LocalFieldTheory LocalFieldTheory.DiscreteValuationField
open scoped ValuativeRel

namespace NAField

/-- The Neu1999 normalized integer valuation, packaged as the
`MultiplicativeIntegerValuation` used by the value-group layer. -/
def multiplicativeIntegerValuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MultiplicativeIntegerValuation Kˣ :=
  LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation K

@[simp] theorem multiplicativeIntegerValuation_val
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    (multiplicativeIntegerValuation K).val x =
      LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul x) :=
  rfl

/-- The Neu1999 normalized integer valuation is onto `ℤ`. -/
theorem multiplicativeIntegerValuation_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (multiplicativeIntegerValuation K).val :=
  open LocalFieldTheory in
  IsNonarchimedeanLocalField.multiplicativeIntegerValuation_surjective K

/-- A Neu1999 local field has a multiplicative element of normalized
valuation one for the value-group API. -/
theorem multiplicativeIntegerValuation_exists_uniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ ϖ : Kˣ, (multiplicativeIntegerValuation K).IsUniformizer ϖ :=
  open LocalFieldTheory in
  IsNonarchimedeanLocalField.multiplicativeIntegerValuation_exists_uniformizer K

/-- The Neu1999 norm-valuation formula, rewritten for the
`LocalFieldTheory.normUnits` API used by the value-group layer. -/
theorem fieldNormUnits_valuation_formula
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    (x : Lˣ) :
    (multiplicativeIntegerValuation K).val (normUnits K L x) =
      (Module.finrank 𝓀[K] 𝓀[L] : ℤ) *
        (multiplicativeIntegerValuation L).val x := by
  change
    LocalFieldTheory.IsNonarchimedeanLocalField.v K
        (Additive.ofMul (normUnits K L x)) =
      (Module.finrank 𝓀[K] 𝓀[L] : ℤ) *
        LocalFieldTheory.IsNonarchimedeanLocalField.v L (Additive.ofMul x)
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
  exact
    LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable K L x

end NAField

end TameAbhyankar

end
