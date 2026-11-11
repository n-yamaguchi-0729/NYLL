/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Integrality detected by the original valuation subrings

The original inverse-adjoin polynomial is shared. The valuation-subring
criterion directly applies Mathlib’s integral-closure intersection theorem
to the original coefficient subring.
-/

@[expose] public section

open Polynomial

/-- If a nonzero field element is a polynomial in its inverse over the given algebra,
then the element is integral over the same coefficient ring. -/
theorem Algebra.isIntegral_of_mem_adjoin_inv {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    {z : F} (hz0 : z ≠ 0) (hmem : z ∈ Algebra.adjoin A ({z⁻¹} : Set F)) : IsIntegral A z := by
  classical
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hp' : aeval z⁻¹ p = z := hp
  have hdeg : (∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ (p.natDegree - i)).degree ≤
      (p.natDegree : WithBot ℕ) := by
    refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast Nat.sub_le _ _)
  refine ⟨X ^ (p.natDegree + 1) - ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^
    (p.natDegree - i),
    Polynomial.monic_X_pow_sub (hdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self _)), ?_⟩
  have hz : z = ∑ i ∈ Finset.range (p.natDegree + 1), algebraMap A F (p.coeff i) * z⁻¹ ^ i := by
    conv_lhs => rw [← hp']
    rw [Polynomial.aeval_eq_sum_range]
    simp only [Algebra.smul_def]
  have hzpow : ∀ i ∈ Finset.range (p.natDegree + 1), z ^ p.natDegree * z⁻¹ ^ i = z ^ (p.natDegree -
    i) := by
    intro i hi
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
    rw [hk, Nat.add_sub_cancel_left, pow_add, mul_comm (z ^ i) (z ^ k), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hz0, one_pow, mul_one]
  rw [eval₂_sub, sub_eq_zero, eval₂_pow, eval₂_X, eval₂_finsetSum]
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [pow_succ]
  conv_lhs => arg 2; rw [hz]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_left_comm, hzpow i hi]

/-- An element belonging to every valuation subring containing the specified subring
is integral over that same subring. -/
theorem Subring.isIntegral_of_mem_all_valuationSubrings {F : Type*} [Field F]
    (A : Subring F) (z : F)
    (h : ∀ V : ValuationSubring F, A ≤ V.toSubring → z ∈ V) : IsIntegral A z := by
  have hz : z ∈ ⨅ V : {V : ValuationSubring F // (A : Set F) ⊆ V.toSubring},
      V.1.toSubring := Subring.mem_iInf.mpr fun V => h V.1 V.2
  rw [iInf_valuationSubring_superset, Subring.closure_eq A] at hz
  exact hz
