/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Valuation.Completion.DVRAdicCompletionIsDomainDVRIsAdicComplete
public import Nyll.SchemeTheory.RingTheory.Smooth.RegularBase
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Generic formal fibres of characteristic-zero discrete valuation rings

Inverting a uniformizer of a DVR gives its fraction field. Consequently
every finite separable extension of the fraction field is étale over the
DVR. Its base change to the completed DVR is regular, using the existing
DVR completion theorem and regularity of smooth algebras over regular
rings.

In characteristic zero this applies to every finite field extension of
the generic residue field. This is a base case for formal-fibre
regularity; it makes no assertion about higher-dimensional coefficient
rings or smooth factorization through their completions.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace IsDiscreteValuationRing

/-- A fraction field of a DVR is already the localization at a
uniformizer. -/
theorem isLocalizationAway_fractionField
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) : IsLocalization.Away π K := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (M := Submonoid.powers π) (S := K) (nonZeroDivisors R) ?_ ?_).mpr
      (inferInstance : IsFractionRing R K)
  · intro x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x π).mp hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hπ.ne_zero)
  · intro x hx
    obtain ⟨n, u, rfl⟩ :=
      eq_unit_mul_pow_irreducible (mem_nonZeroDivisors_iff_ne_zero.mp hx) hπ
    refine ⟨π ^ n, (Submonoid.powers π).pow_mem (Submonoid.mem_powers π) n, ?_⟩
    exact Units.mul_left_dvd.mpr (dvd_refl (π ^ n))

/-- Every finite separable extension of the generic residue field gives
a regular base change of the completed DVR. -/
theorem adicCompletion_tensor_isRegularRing_of_isSeparable
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] :
    IsRegularRing (AdicCompletion (IsLocalRing.maximalIdeal R) R ⊗[R] L) := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have : IsLocalization.Away π K := isLocalizationAway_fractionField R K π hπ
  have : Algebra.Etale R K := Algebra.Etale.of_isLocalizationAway π
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.FinitePresentation K L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  have : Algebra.Etale R L := Algebra.Etale.comp R K L
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
  obtain ⟨hCdomain, hCdvr, _, _⟩ :=
    adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete R π hπ
  have : IsDomain C := hCdomain
  have : IsDiscreteValuationRing C := hCdvr
  have : IsRegularRing C := inferInstance
  exact Algebra.Smooth.isRegularRing_of_isRegularRing C (C ⊗[R] L)

/-- The generic formal fibre of a characteristic-zero DVR remains
regular after every finite field extension of its fraction field. -/
theorem adicCompletion_genericFiber_isRegularRing_of_charZero
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L] :
    IsRegularRing (AdicCompletion (IsLocalRing.maximalIdeal R) R ⊗[R] L) := by
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  exact adicCompletion_tensor_isRegularRing_of_isSeparable R K L

end IsDiscreteValuationRing
