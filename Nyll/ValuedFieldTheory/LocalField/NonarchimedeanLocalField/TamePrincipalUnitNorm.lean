/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitRoots
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparablePrincipalUnitNorm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.Ramification.Different.Powers

/-!
# Exact principal-unit norms when the extension degree is a unit

Hensel lifting supplies a root of the extension degree inside the specified
base principal-unit group. Its image upstairs has depth multiplied by the
ramification index, and its actual norm is the original unit. This includes
the totally ramified tame factor of a general tame extension.
-/

@[expose] public section

noncomputable section

universe u v

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

section IntegerRing

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The integer-unit norm of an embedded base unit is its extension-degree power. -/
theorem normIntegerUnits_integerUnitsMap (z : 𝒪[K]ˣ) :
    normIntegerUnits K L (integerUnitsMapOfValuationExtension K L z) =
      z ^ Module.finrank K L := by
  apply Units.ext
  apply Subtype.ext
  rw [Units.val_pow_eq_pow_val]
  change Algebra.norm K (algebraMap K L (z : K)) =
    algebraMap 𝒪[K] K ((z : 𝒪[K]) ^ Module.finrank K L)
  rw [Algebra.norm_algebraMap, map_pow]
  rfl

/-- When the extension degree is a unit, the norm image is exactly the
principal-unit level specified by `e * (m - 1) < r ≤ e * m`. -/
theorem principalUnits_map_norm_eq_of_isUnit_finrank
    (hd : IsUnit (Module.finrank K L : 𝒪[K])) {r m : ℕ} (hm : 1 ≤ m)
    (hlo : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r)
    (hhi : r ≤ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * m) :
    (principalUnits L r).map (normIntegerUnits K L) = principalUnits K m := by
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    integerRing_algebra_isIntegral_of_isIntegralClosure K L
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact normIntegerUnits_mem_principalUnits_of_depth_of_isSeparable K L hlo ha
  · intro a ha
    obtain ⟨z, hz, hzpow⟩ :=
      exists_principalUnit_pow_eq_of_isUnit_natCast K (Module.finrank K L) hd hm ha
    have hzL : integerUnitsMapOfValuationExtension K L z ∈
        principalUnits L ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * m) := by
      have h := RamificationTheory.DiscreteValuationRing.map_mem_maximalIdeal_pow_mul
        𝒪[K] 𝒪[L] hz
      change algebraMap 𝒪[K] 𝒪[L] ((z : 𝒪[K]) - 1) ∈
        (𝓂[L] ^ ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * m) : Ideal 𝒪[L]) at h
      rw [map_sub, map_one] at h
      exact h
    refine ⟨integerUnitsMapOfValuationExtension K L z,
      principalUnits_antitone L hhi hzL, ?_⟩
    rw [normIntegerUnits_integerUnitsMap]
    exact hzpow

end IntegerRing

/-- The same exact norm image on actual field units. The integral-closure
identification is supplied by finite separability. -/
theorem fieldPrincipalUnits_map_norm_eq_of_isUnit_finrank
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (hd : IsUnit (Module.finrank K L : 𝒪[K])) {r m : ℕ} (hm : 1 ≤ m)
    (hlo : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r)
    (hhi : r ≤ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * m) :
    (fieldPrincipalUnits L r).map (normUnits K L) = fieldPrincipalUnits K m := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  change ((principalUnits L r).map (integerUnitsToFieldUnits L)).map (normUnits K L) = _
  rw [Subgroup.map_map]
  have hcomp : (normUnits K L).comp (integerUnitsToFieldUnits L) =
      (integerUnitsToFieldUnits K).comp (normIntegerUnits K L) := rfl
  rw [hcomp, ← Subgroup.map_map, principalUnits_map_norm_eq_of_isUnit_finrank K L hd hm hlo hhi]
  rfl

end LocalFieldTheory
