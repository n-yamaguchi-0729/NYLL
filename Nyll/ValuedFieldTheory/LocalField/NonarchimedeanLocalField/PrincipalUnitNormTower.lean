/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NormUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.TamePrincipalUnitNorm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedPrincipalUnits.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedPrincipalUnits.Lift

/-!
# Principal-unit norm images in unramified towers

The existing approximation proof gives the full image in an unramified
extension. Actual field-norm transitivity then composes it with the
prime-to-degree result for the upper extension.
-/

@[expose] public section

noncomputable section

universe u v w

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open LocalClassFieldTheory
  (normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure)

/-- The existing unramified surjectivity theorem as an equality of actual field-unit images. -/
theorem fieldPrincipalUnits_map_norm_eq_of_unramified
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] {r : ℕ} (hr : 1 ≤ r) :
    (fieldPrincipalUnits L r).map (normUnits K L) = fieldPrincipalUnits K r := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨normIntegerUnits K L a,
      normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure K L r a ha,
      rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb⟩ :=
      LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
        K L r hr ⟨a, ha⟩
    refine ⟨integerUnitsToFieldUnits L b.1, ⟨b.1, b.2, rfl⟩, ?_⟩
    change integerUnitsToFieldUnits K (normIntegerUnits K L b.1) = integerUnitsToFieldUnits K a
    exact congrArg (integerUnitsToFieldUnits K) (congrArg Subtype.val hb)

/-- Norm images compose across an unramified lower extension and an upper
extension whose degree is a unit, at every positive compatible depth. -/
theorem fieldPrincipalUnits_map_norm_eq_of_unramified_tower
    (K : Type u) (T : Type v) (L : Type w)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field T] [ValuativeRel T] [UniformSpace T] [IsUniformAddGroup T]
    [IsNonarchimedeanLocalField T]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K T] [Algebra T L] [Algebra K L] [IsScalarTower K T L]
    [FiniteDimensional K T] [IsGalois K T]
    [FiniteDimensional T L] [Algebra.IsSeparable T L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation T)]
    [Valuation.HasExtension (ValuativeRel.valuation T) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[T] 𝒪[K] T] [Module.Finite 𝒪[K] 𝒪[T]]
    [IsUnramifiedValuedExtension K T]
    (hd : IsUnit (Module.finrank T L : 𝒪[T])) {r m : ℕ} (hm : 1 ≤ m)
    (hlo : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[T] * (m - 1) < r)
    (hhi : r ≤ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[T] * m) :
    (fieldPrincipalUnits L r).map (normUnits K L) = fieldPrincipalUnits K m := by
  have hcomp : normUnits K L = (normUnits K T).comp (normUnits T L) := by
    apply MonoidHom.ext
    intro a
    exact (normUnits_tower K T L a).symm
  rw [hcomp, ← Subgroup.map_map,
    fieldPrincipalUnits_map_norm_eq_of_isUnit_finrank T L hd hm hlo hhi,
    fieldPrincipalUnits_map_norm_eq_of_unramified K T hm]

end LocalFieldTheory
