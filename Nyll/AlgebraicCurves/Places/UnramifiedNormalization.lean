/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqRamificationIdxFiberCenter
public import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRNormalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Separable
public import Mathlib.FieldTheory.Perfect

/-!
# Étale normalization from original unramified places

The original place/prime correspondence identifies the ramification index
at every maximal ideal of the integral closure. A perfect original residue
field supplies residue separability, so the established DVR criterion
makes that same integral closure étale.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve.Place

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- If the original place has perfect residue field and every extending
place has ramification index one, its actual integral closure is étale. -/
theorem integralClosure_etale_of_ramificationIndex_eq_one
    (v : Place k K) [PerfectField v.ResidueField]
    (he : ∀ w : Place k L, w.restrict K = v → w.ramificationIndex K = 1) :
    Algebra.Etale v.toValuationSubring (integralClosureAt L v) := by
  let R := v.toValuationSubring
  let B := integralClosureAt L v
  let ι : IsLocalRing.ResidueField R →+*
      (IsLocalRing.maximalIdeal R).ResidueField :=
    algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal R).ResidueField
  have hperfect : PerfectField (IsLocalRing.maximalIdeal R).ResidueField :=
    PerfectField.of_ringEquiv (K := IsLocalRing.ResidueField R) (RingEquiv.ofBijective ι
      (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R)))
  apply (SchemeTheory.finite_etale_integralClosure_of_unramifiedOverDVR R K L ?_).2
  intro P hP
  let : Algebra (Localization.AtPrime (P.under R)) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have hbase : P.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal inferInstance
  have : PerfectField (P.under R).ResidueField :=
    PerfectField.of_ringEquiv
      (Ideal.residueFieldRingEquiv (IsLocalRing.maximalIdeal R) (P.under R)
        (RingEquiv.refl R)
        (hbase.symm.trans (Ideal.comap_id (P.under R)).symm))
  refine ⟨inferInstance, ?_⟩
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro hm
    exact IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)
  have hunderne : P.under R ≠ ⊥ := by
    intro hzero
    exact hm (hbase.symm.trans hzero)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunderne P
  let Q : IsDedekindDomain.HeightOneSpectrum B := ⟨P, inferInstance, hPne⟩
  have hw := restrict_placeOfPrime (F' := L) (v := v) Q
  have hindex := ramificationIndex_eq_ramificationIdx_fiberCenter v hw
  rw [fiberCenter_placeOfPrime] at hindex
  change (placeOfPrime Q).ramificationIndex K =
    (IsLocalRing.maximalIdeal R).ramificationIdx' P at hindex
  rw [hbase, ← hindex]
  exact he (placeOfPrime Q) hw

end AlgebraicCurve.Place
