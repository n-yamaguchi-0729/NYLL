/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.InertiaSubfield
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitNormTower
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitOrder
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.NormUnits
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Tame norms at every positive principal-unit depth

The actual inertia fixed field supplies the unramified factor. The upper
factor has unit degree, so Hensel roots and the actual norm tower give the
exact image. Strictness of principal-unit levels determines the least
positive depth with prescribed norm containment.
-/

@[expose] public section

noncomputable section

universe u v

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- A finite tame Galois norm has the full principal-unit image at every
positive depth in the interval `e * (m - 1) < r ≤ e * m`. -/
theorem fieldPrincipalUnits_norm_map_eq_of_tame
    (htame : ¬ ringChar 𝓀[K] ∣ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])
    {r m : ℕ} (hm : 1 ≤ m)
    (hlo : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r)
    (hhi : r ≤ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * m) :
    (fieldPrincipalUnits L r).map (normUnits K L) = fieldPrincipalUnits K m := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  let T := inertiaSubfield K L
  let : NontriviallyNormedField T := inertiaSubfieldNormedField K L
  let : UniformSpace T := inertiaSubfieldUniformSpace K L
  let : TopologicalSpace T := inertiaSubfieldTopologicalSpace K L
  let : ValuativeRel T := inertiaSubfieldValuativeRel K L
  let : IsNonarchimedeanLocalField T := inertiaSubfieldIsNonarchimedeanLocalField K L
  let : IsGalois K T := inertiaSubfield_isGalois K L
  let : IsGalois T L := inertiaSubfield_top_isGalois K L
  let : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation T) :=
    inertiaSubfield_base_hasExtension K L
  let : (ValuativeRel.valuation T).HasExtension (ValuativeRel.valuation L) :=
    inertiaSubfield_top_hasExtension K L
  let : IsIntegralClosure 𝒪[T] 𝒪[K] T := inertiaSubfield_base_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[T] := inertiaSubfield_base_moduleFinite K L
  let : IsUnramifiedValuedExtension K T := inertiaSubfield_isUnramified K L
  have heunit : IsUnit ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] : 𝒪[K]) := by
    apply isUnit_of_map_unit (IsLocalRing.residue 𝒪[K])
    rw [map_natCast]
    apply isUnit_iff_ne_zero.mpr
    exact fun h => htame ((ringChar.spec (R := 𝓀[K]) _).mp h)
  have hd : IsUnit (Module.finrank T L : 𝒪[T]) := by
    rw [show Module.finrank T L = (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] from
      finrank_inertiaSubfield K L]
    simpa only [map_natCast] using heunit.map (algebraMap 𝒪[K] 𝒪[T])
  have hidx : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[T] =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] :=
    inertiaSubfield_top_ramificationIdx K L
  apply fieldPrincipalUnits_map_norm_eq_of_unramified_tower K T L hd hm
  · rw [hidx]
    exact hlo
  · rw [hidx]
    exact hhi

/-- At positive depth, the tame norm image is the ceiling level `ceil(r / e)`. -/
theorem fieldPrincipalUnits_norm_map_eq_ceil_of_tame
    (htame : ¬ ringChar 𝓀[K] ∣ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])
    {r : ℕ} (hr : 1 ≤ r) :
    (fieldPrincipalUnits L r).map (normUnits K L) =
      fieldPrincipalUnits K ((r - 1) / (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] + 1) := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    integerRing_algebra_isIntegral_of_isIntegralClosure K L
  have he := Ideal.ramificationIdx_pos 𝒪[K] (𝓂[L] : Ideal 𝒪[L])
  apply fieldPrincipalUnits_norm_map_eq_of_tame K L htame (Nat.succ_pos _)
  · have hfloor := Nat.div_mul_le_self (r - 1)
      ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])
    rw [Nat.succ_sub_one, Nat.mul_comm]
    exact lt_of_le_of_lt hfloor (Nat.sub_lt (Nat.succ_le_iff.mp hr) Nat.one_pos)
  · calc
      r = (r - 1) + 1 := (Nat.sub_add_cancel hr).symm
      _ ≤ _ := Nat.succ_le_of_lt (Nat.lt_mul_div_succ (r - 1) he)

/-- Tame norm containment at positive depths is equivalent to the sharp
arithmetic bound `e * (m - 1) + 1 ≤ r`. -/
theorem fieldPrincipalUnits_norm_map_le_iff_of_tame
    (htame : ¬ ringChar 𝓀[K] ∣ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])
    {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (fieldPrincipalUnits L r).map (normUnits K L) ≤ fieldPrincipalUnits K m ↔
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) + 1 ≤ r := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    integerRing_algebra_isIntegral_of_isIntegralClosure K L
  have he := Ideal.ramificationIdx_pos 𝒪[K] (𝓂[L] : Ideal 𝒪[L])
  rw [fieldPrincipalUnits_norm_map_eq_ceil_of_tame K L htame hr,
    fieldPrincipalUnits_le_iff K (Nat.succ_pos _)]
  have horder : m ≤ (r - 1) / (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] + 1 ↔
      m - 1 ≤ (r - 1) / (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by omega
  rw [horder, Nat.le_div_iff_mul_le he, Nat.mul_comm]
  omega

/-- The least positive source depth for tame norm containment is
`e * (m - 1) + 1`. -/
theorem isLeast_principalUnitNormDepth_of_tame
    (htame : ¬ ringChar 𝓀[K] ∣ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])
    {m : ℕ} (hm : 1 ≤ m) :
    IsLeast {r : ℕ | 1 ≤ r ∧
      (fieldPrincipalUnits L r).map (normUnits K L) ≤ fieldPrincipalUnits K m}
      ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) + 1) := by
  refine ⟨⟨Nat.succ_pos _, ?_⟩, ?_⟩
  · exact (fieldPrincipalUnits_norm_map_le_iff_of_tame K L htame (Nat.succ_pos _) hm).mpr le_rfl
  · intro r hr
    exact (fieldPrincipalUnits_norm_map_le_iff_of_tame K L htame hr.1 hm).mp hr.2

end LocalFieldTheory
