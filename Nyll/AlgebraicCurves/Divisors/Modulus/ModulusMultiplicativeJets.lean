/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusJets

/-!
# Multiplicative approximation with zeros and poles

A finite list of nonzero rational functions can be interpolated multiplicatively
at prescribed places, modulo the full maximal-ideal powers. The germs being
interpolated need not be local units. Thus a test function for a local symbol can
retain a specified zero or pole at one place while being congruent to one at all
the other places in the modulus.

The input approximation theorem is the proved place approximation imported by
`ModulusJets`; no approximation assumption or local-symbol existence is added.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

/-- At positive precision, the valuation bound on `f - 1` is equivalent to the
actual local-unit congruence. This implication also proves that `f` is nonzero. -/
theorem congruentOne_iff_adicValuation_sub_one_le (v : Place K F)
    {n : ℕ} (hn : n ≠ 0) (f : F) :
    v.CongruentOne n f ↔
      v.adicValuation (f - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨u, rfl, hu⟩
    rw [← v.heightOneSpectrum_asIdeal,
      ← v.heightOneSpectrum.intValuation_le_pow_iff_mem, ← v.adicValuation_coe] at hu
    exact hu
  · intro hbound
    have hboundOne : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      exact neg_nonpos.mpr (Nat.cast_nonneg n)
    have hdiff : f - 1 ∈ v.toValuationSubring :=
      v.mem_iff_adicValuation_le_one.mpr (hbound.trans hboundOne)
    have hmem : f ∈ v.toValuationSubring := by
      have h := add_mem hdiff (one_mem v.toValuationSubring)
      simpa only [sub_add_cancel] using h
    let a : v.toValuationSubring := ⟨f, hmem⟩
    have hpow : a - 1 ∈ (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n := by
      rw [← v.heightOneSpectrum_asIdeal,
        ← v.heightOneSpectrum.intValuation_le_pow_iff_mem, ← v.adicValuation_coe]
      exact hbound
    have hjet : Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n) a = 1 := by
      rw [← (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)).map_one]
      exact Ideal.Quotient.eq.mpr hpow
    let : IsLocalHom (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)) :=
      v.unitReduction_isLocalHom hn
    have ha : IsUnit a := isUnit_of_map_unit
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)) a
      (by rw [hjet]; exact isUnit_one)
    refine ⟨ha.unit, ?_, ?_⟩
    · rw [IsUnit.unit_spec]
    · rw [IsUnit.unit_spec]
      exact hpow

/-- Multiplicative weak approximation preserves arbitrary prescribed zeros,
poles, and higher unit jets at finitely many distinct places. -/
theorem exists_multiplicative_jets (S : Finset (Place K F))
    (g : Place K F → F) (hg : ∀ v ∈ S, g v ≠ 0) (n : Place K F → ℕ) :
    ∃ f : F, f ≠ 0 ∧ ∀ v ∈ S, v.CongruentOne (n v) (f / g v) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨1, one_ne_zero, fun v hv => (Finset.notMem_empty v hv).elim⟩
  obtain ⟨f, hf⟩ := exists_forall_adicValuation_sub_le S g
    (fun v => -((n v + 1 : ℕ) : ℤ) - v.ord (g v))
  have hlocal (v : Place K F) (hv : v ∈ S) :
      v.CongruentOne (n v + 1) (f / g v) := by
    apply (v.congruentOne_iff_adicValuation_sub_one_le (Nat.succ_ne_zero (n v)) _).mpr
    have heq : f / g v - 1 = (f - g v) * (g v)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ (hg v hv), div_eq_mul_inv]
    rcases (v.adicValuation_le_exp_iff).mp (hf v hv) with he | hord
    · exact (v.adicValuation_le_exp_iff).mpr (Or.inl (by rw [heq, he, zero_mul]))
    · by_cases he : f - g v = 0
      · exact (v.adicValuation_le_exp_iff).mpr (Or.inl (by rw [heq, he, zero_mul]))
      · apply (v.adicValuation_le_exp_iff).mpr
        right
        rw [heq, v.ord_mul he (inv_ne_zero (hg v hv)), v.ord_inv]
        omega
  refine ⟨f, ?_, fun v hv => (hlocal v hv).mono (Nat.le_succ (n v))⟩
  obtain ⟨v, hv⟩ := hS
  intro hfzero
  have hn := (hlocal v hv).ne_zero
  exact hn (by rw [hfzero, zero_div])

/-- A local-symbol test function can match one arbitrary nonzero germ and be
congruent to one to all prescribed orders at the other finitely many places. -/
theorem exists_multiplicative_jet_isolated (S : Finset (Place K F))
    (v : Place K F) (g : F) (hg : g ≠ 0) (n : Place K F → ℕ) :
    ∃ f : F, f ≠ 0 ∧ v.CongruentOne (n v) (f / g) ∧
      ∀ w ∈ S, w ≠ v → w.CongruentOne (n w) f := by
  classical
  obtain ⟨f, hf, hlocal⟩ := exists_multiplicative_jets (insert v S)
    (fun w => if w = v then g else 1)
    (fun w _ => by
      split_ifs
      · exact hg
      · exact one_ne_zero) n
  refine ⟨f, hf, ?_, ?_⟩
  · have h := hlocal v (Finset.mem_insert_self v S)
    have he : (if v = v then g else 1) = g := ite_eq_left rfl
    rw [he] at h
    exact h
  · intro w hw hwv
    simpa only [ite_eq_right hwv, div_one] using hlocal w (Finset.mem_insert_of_mem hw)

end Place

end AlgebraicCurve
