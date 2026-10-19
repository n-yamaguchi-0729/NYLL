/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusLocalUnits
import Nyll.AlgebraicCurves.Places.Orders.AdicValuationSubLe
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# Interpolation of finite local-unit jets

Weak approximation for distinct places supplies simultaneous congruences
modulo arbitrary maximal-ideal powers. Thus the multiplicities of a modulus
are retained, including at nonreduced support. The interpolating function is
proved to be a unit at every supported place and globally nonzero.

The approximation theorem is supplied by
`Places.Place_exists_forall_adicValuation_sub_le`, which retains its upstream
Anthropic FLT attribution. This file applies that theorem without introducing
any additional approximation hypothesis.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

open LubinTate.Valuations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Any finite system of local-unit jets, with the full multiplicities of a
modulus, is represented by one nonzero rational function. -/
theorem exists_unit_jets (D : Modulus K F)
    (u : ∀ v : Place K F, v.toValuationSubringˣ) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v ≠ 0 →
      ∃ w : v.toValuationSubringˣ,
        ((w : v.toValuationSubring) : F) = f ∧
          unitReduction ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v)) w =
            unitReduction ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v)) (u v) := by
  classical
  rcases D.support.eq_empty_or_nonempty with hD | hD
  · refine ⟨1, one_ne_zero, fun v hv => ?_⟩
    have h := Finsupp.mem_support_iff.mpr hv
    simp [hD] at h
  · obtain ⟨f, hf⟩ := Place.exists_forall_adicValuation_sub_le D.support
      (fun v => ((u v : v.toValuationSubring) : F)) (fun v => -(D v : ℤ))
    have hlocal : ∀ v : Place K F, D v ≠ 0 →
        ∃ w : v.toValuationSubringˣ,
          ((w : v.toValuationSubring) : F) = f ∧
            unitReduction ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v)) w =
              unitReduction ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v)) (u v) := by
      intro v hv
      have hbound := hf v (Finsupp.mem_support_iff.mpr hv)
      have hboundOne : WithZero.exp (-(D v : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        exact neg_nonpos.mpr (Nat.cast_nonneg _)
      have hdiff : f - ((u v : v.toValuationSubring) : F) ∈ v.toValuationSubring :=
        v.mem_iff_adicValuation_le_one.mpr (hbound.trans hboundOne)
      have hmem : f ∈ v.toValuationSubring := by
        have h := add_mem hdiff (u v).val.2
        simpa only [sub_add_cancel] using h
      let a : v.toValuationSubring := ⟨f, hmem⟩
      have hdiffPow : a - (u v : v.toValuationSubring) ∈
          (IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v) := by
        rw [← v.heightOneSpectrum_asIdeal,
          ← v.heightOneSpectrum.intValuation_le_pow_iff_mem, ← v.adicValuation_coe]
        exact hbound
      have hjet : Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v)) a =
          Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v)) (u v) :=
        Ideal.Quotient.eq.mpr hdiffPow
      let : IsLocalHom (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v))) :=
        v.unitReduction_isLocalHom hv
      have ha : IsUnit a := isUnit_of_map_unit
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (D v))) a
        (by rw [hjet]; exact (u v).isUnit.map _)
      refine ⟨ha.unit, ?_, ?_⟩
      · rw [IsUnit.unit_spec]
      · apply Units.ext
        change Ideal.Quotient.mk _ (ha.unit : v.toValuationSubring) =
          Ideal.Quotient.mk _ (u v : v.toValuationSubring)
        rw [IsUnit.unit_spec]
        exact hjet
    refine ⟨f, ?_, hlocal⟩
    obtain ⟨v, hv⟩ := hD
    obtain ⟨w, hw, _⟩ := hlocal v (Finsupp.mem_support_iff.mp hv)
    rw [← hw]
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using w.ne_zero

end AlgebraicCurve.Modulus
