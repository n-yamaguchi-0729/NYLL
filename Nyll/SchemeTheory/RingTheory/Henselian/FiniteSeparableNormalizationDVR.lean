/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.HenselianIntegralDomainLocal
import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual normalization of a strictly Henselian DVR

For a finite separable extension of its fraction field, the integral
closure of a strictly Henselian DVR is again a strictly Henselian DVR,
finite over the original ring, with the displayed extension field as
its fraction field.

The trace argument makes the integral closure finite and Dedekind.
Henselianity of the base makes the integral domain local. An injective
integral extension cannot turn the base DVR into a field. These facts
prove discreteness of the normalization. Finally, its finite residue
extension is separably closed because the original residue field is.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- The integral closure in a finite separable coefficient extension is
an actual finite strictly Henselian DVR, with the prescribed fraction
field and the native local map from the original DVR. -/
theorem finiteSeparableNormalization_strictHenselianDVR
    (B : Type u) (K : Type v) (L : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    [Field K] [Field L] [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    let C := integralClosure B L
    let : IsLocalRing C := isLocalRing_of_integral_domain_henselian B C
    Module.Finite B C ∧ IsFractionRing C L ∧ IsDiscreteValuationRing C ∧
      HenselianLocalRing C ∧ IsSepClosed (IsLocalRing.ResidueField C) ∧
        IsLocalHom (algebraMap B C) := by
  intro C hLocal
  have hFinite : Module.Finite B C := IsIntegralClosure.finite B K L C
  have hFraction : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension B K L C
  have : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain B K L C
  have hBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  have hBC : Function.Injective (algebraMap B C) := by
    intro x y hxy
    apply hBL
    rw [IsScalarTower.algebraMap_apply B C L, IsScalarTower.algebraMap_apply B C L]
    exact congrArg (algebraMap C L) hxy
  have : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr hBC
  have hMap : IsLocalHom (algebraMap B C) := inferInstance
  have hNotField : ¬ IsField C := fun h => IsDiscreteValuationRing.not_isField B
    (isField_of_isIntegral_of_isField hBC h)
  have hDVR : IsDiscreteValuationRing C :=
    ((IsDiscreteValuationRing.TFAE C hNotField).out 1 3).mpr
      (inferInstance : IsDedekindDomain C)
  have hHenselian : HenselianLocalRing C :=
    HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := B) (S := C)
  have hResidue : IsSepClosed (IsLocalRing.ResidueField C) :=
    Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField B)
      (E := IsLocalRing.ResidueField C)
  exact ⟨hFinite, hFraction, hDVR, hHenselian, hResidue, hMap⟩

end SchemeTheory
