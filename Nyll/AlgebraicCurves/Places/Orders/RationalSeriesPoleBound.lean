/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! # Linear pole bounds from finite rational-coordinate data

The bound is computed from polynomial coefficients. The power-series inverse
recursion, rather than an assumed growth condition, supplies the estimate.
Formal translation works in every characteristic and does not divide by
factorials. This is an algebraic input to boundary arguments, not a global
reciprocity or extension theorem. On an arbitrary curve, a formal diagonal
or finite étale lifting must still connect its actual coordinates to such
formal expansions; functions need not be rational in a local parameter.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- A computable finite integer bound on the orders of polynomial coefficients. -/
def polynomialOrderBound (P : Polynomial F) : ℕ :=
  ∑ i ∈ P.support, (v.ord (P.coeff i)).natAbs

private theorem ord_add_lower (a b : F) (B : ℕ)
    (ha : -(B : ℤ) ≤ v.ord a) (hb : -(B : ℤ) ≤ v.ord b) :
    -(B : ℤ) ≤ v.ord (a + b) := by
  by_cases ha0 : a = 0
  · simpa only [ha0, zero_add] using hb
  by_cases hb0 : b = 0
  · simpa only [hb0, add_zero] using ha
  by_cases hab0 : a + b = 0
  · rw [hab0, v.ord_zero]
    omega
  exact (le_min ha hb).trans (v.min_ord_le_ord_add ha0 hb0 hab0)

/-- A common nonpositive order bound is preserved by finite sums, including zero terms. -/
theorem ord_finset_sum_ge_neg_bound {ι : Type*} (s : Finset ι) (f : ι → F) (B : ℕ)
    (hf : ∀ i ∈ s, -(B : ℤ) ≤ v.ord (f i)) :
    -(B : ℤ) ≤ v.ord (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, v.ord_zero]
    omega
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ord_add_lower v _ _ B (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The sum of two pole bounds bounds the product, including zero factors. -/
theorem ord_mul_ge_neg_bounds (a b : F) (A B : ℕ)
    (ha : -(A : ℤ) ≤ v.ord a) (hb : -(B : ℤ) ≤ v.ord b) :
    -((A + B : ℕ) : ℤ) ≤ v.ord (a * b) := by
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul, v.ord_zero]
    omega
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, v.ord_zero]
    omega
  rw [v.ord_mul ha0 hb0, Nat.cast_add]
  omega

/-- The finite coefficient sum bounds both signs of every coefficient order. -/
theorem polynomial_coeff_ord_bounds (P : Polynomial F) (i : ℕ) :
    -(v.polynomialOrderBound P : ℤ) ≤ v.ord (P.coeff i) ∧
      v.ord (P.coeff i) ≤ (v.polynomialOrderBound P : ℤ) := by
  classical
  have hi : (v.ord (P.coeff i)).natAbs ≤ v.polynomialOrderBound P := by
    by_cases his : i ∈ P.support
    · change (v.ord (P.coeff i)).natAbs ≤ ∑ j ∈ P.support, (v.ord (P.coeff j)).natAbs
      exact Finset.single_le_sum (fun j _ => Nat.zero_le ((v.ord (P.coeff j)).natAbs)) his
    · have hc : P.coeff i = 0 := by
        by_contra hc
        exact his (Polynomial.mem_support_iff.mpr hc)
      rw [hc, v.ord_zero, Int.natAbs_zero]
      exact Nat.zero_le _
  have hi' : ((v.ord (P.coeff i)).natAbs : ℤ) ≤
      (v.polynomialOrderBound P : ℤ) := by exact_mod_cast hi
  have hp : v.ord (P.coeff i) ≤ ((v.ord (P.coeff i)).natAbs : ℤ) := Int.le_natAbs
  have hn : -v.ord (P.coeff i) ≤ ((v.ord (P.coeff i)).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -v.ord (P.coeff i)))
  omega

/-- The actual formal inverse has at most linear coefficient poles. The
constant is obtained from the finite denominator, including its constant term. -/
theorem polynomial_inverse_coeff_ord_lower (Q : Polynomial F) (n : ℕ) :
    -((v.polynomialOrderBound Q * (2 * n + 1) : ℕ) : ℤ) ≤
      v.ord (PowerSeries.coeff n ((Q : PowerSeries F)⁻¹)) := by
  let B := v.polynomialOrderBound Q
  change -((B * (2 * n + 1) : ℕ) : ℤ) ≤ _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [PowerSeries.coeff_inv, ite_eq_left rfl, Polynomial.constantCoeff_coe,
        v.ord_inv]
      simpa only [mul_zero, zero_add, mul_one] using
        neg_le_neg (polynomial_coeff_ord_bounds v Q 0).2
    rw [PowerSeries.coeff_inv, ite_eq_right hn, Polynomial.constantCoeff_coe]
    have hc : -(B : ℤ) ≤ v.ord (-(Q.coeff 0)⁻¹) := by
      simp only [Place.ord, Valuation.map_neg]
      change -(B : ℤ) ≤ v.ord ((Q.coeff 0)⁻¹)
      rw [v.ord_inv]
      exact neg_le_neg (polynomial_coeff_ord_bounds v Q 0).2
    have hs : -((2 * B * n : ℕ) : ℤ) ≤
        v.ord (∑ x ∈ Finset.antidiagonal n,
          if x.2 < n then PowerSeries.coeff x.1 (Q : PowerSeries F) *
            PowerSeries.coeff x.2 ((Q : PowerSeries F)⁻¹) else 0) := by
      apply ord_finset_sum_ge_neg_bound v _ _ (2 * B * n)
      intro x _
      by_cases hx : x.2 < n
      · rw [ite_eq_left hx]
        have hprod := ord_mul_ge_neg_bounds v _ _ B (B * (2 * x.2 + 1))
          (by simpa only [Polynomial.coeff_coe] using
            (polynomial_coeff_ord_bounds v Q x.1).1) (ih x.2 hx)
        have hle : B + B * (2 * x.2 + 1) ≤ 2 * B * n := by
          have hm := Nat.mul_le_mul_left B (show 2 * x.2 + 2 ≤ 2 * n by omega)
          nlinarith
        have hle' : ((B + B * (2 * x.2 + 1) : ℕ) : ℤ) ≤
            ((2 * B * n : ℕ) : ℤ) := by exact_mod_cast hle
        rw [Polynomial.coeff_coe]
        exact (neg_le_neg hle').trans hprod
      · rw [ite_eq_right hx, v.ord_zero]
        omega
    have hm := ord_mul_ge_neg_bounds v _ _ B (2 * B * n) hc hs
    have he : B + 2 * B * n = B * (2 * n + 1) := by ring
    simpa only [he] using hm

/-- Numerator and denominator supply an explicit coefficient bound for their
formal quotient; no coefficient-bound hypothesis is needed. -/
theorem polynomial_quotient_coeff_ord_lower (P Q : Polynomial F) (n : ℕ) :
    -((v.polynomialOrderBound P + v.polynomialOrderBound Q * (2 * n + 1) : ℕ) : ℤ) ≤
      v.ord (PowerSeries.coeff n ((P : PowerSeries F) * (Q : PowerSeries F)⁻¹)) := by
  rw [PowerSeries.coeff_mul]
  apply ord_finset_sum_ge_neg_bound v _ _ _
  intro x hx
  have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
  have hm := ord_mul_ge_neg_bounds v _ _ (v.polynomialOrderBound P)
    (v.polynomialOrderBound Q * (2 * x.2 + 1))
    (by simpa only [Polynomial.coeff_coe] using (polynomial_coeff_ord_bounds v P x.1).1)
    (polynomial_inverse_coeff_ord_lower v Q x.2)
  have hle : v.polynomialOrderBound P + v.polynomialOrderBound Q * (2 * x.2 + 1) ≤
      v.polynomialOrderBound P + v.polynomialOrderBound Q * (2 * n + 1) := by
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul_left _ (by omega)
  have hle' :
      ((v.polynomialOrderBound P + v.polynomialOrderBound Q * (2 * x.2 + 1) : ℕ) : ℤ) ≤
      ((v.polynomialOrderBound P + v.polynomialOrderBound Q * (2 * n + 1) : ℕ) : ℤ) := by
    exact_mod_cast hle
  rw [Polynomial.coeff_coe]
  exact (neg_le_neg hle').trans hm

/-- A genuine rational formal expansion satisfies its denominator equation
and a linear pole estimate derived from its finite polynomial data. -/
theorem polynomial_quotient_linear_pole_bound
    (P Q : Polynomial F) (hQ : Q.coeff 0 ≠ 0) :
    let S := (P : PowerSeries F) * (Q : PowerSeries F)⁻¹
    let C := v.polynomialOrderBound P + 2 * v.polynomialOrderBound Q
    S * (Q : PowerSeries F) = (P : PowerSeries F) ∧
      ∀ n : ℕ, -((C * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n S) := by
  intro S C
  constructor
  · change ((P : PowerSeries F) * (Q : PowerSeries F)⁻¹) * (Q : PowerSeries F) = _
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
      simpa only [Polynomial.constantCoeff_coe] using hQ), mul_one]
  · intro n
    have h := polynomial_quotient_coeff_ord_lower v P Q n
    have hle : v.polynomialOrderBound P + v.polynomialOrderBound Q * (2 * n + 1) ≤
        C * (n + 1) := by
      dsimp only [C]
      nlinarith
    have hle' :
        ((v.polynomialOrderBound P + v.polynomialOrderBound Q * (2 * n + 1) : ℕ) : ℤ) ≤
        ((C * (n + 1) : ℕ) : ℤ) := by exact_mod_cast hle
    dsimp only [S]
    exact (neg_le_neg hle').trans h

/-- One constant, computed from a finite list of rational coordinates, bounds
all their formal expansions. Each denominator is inverted as an actual series. -/
theorem polynomial_quotient_family_linear_pole_bound
    {ι : Type*} [Fintype ι] (P Q : ι → Polynomial F)
    (hQ : ∀ i, (Q i).coeff 0 ≠ 0) :
    let S := fun i => (P i : PowerSeries F) * (Q i : PowerSeries F)⁻¹
    let C := ∑ i, (v.polynomialOrderBound (P i) + 2 * v.polynomialOrderBound (Q i))
    ∀ i, S i * (Q i : PowerSeries F) = (P i : PowerSeries F) ∧
      ∀ n : ℕ, -((C * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (S i)) := by
  classical
  intro S C i
  obtain ⟨heq, hbound⟩ := polynomial_quotient_linear_pole_bound v (P i) (Q i) (hQ i)
  refine ⟨heq, ?_⟩
  intro n
  have hi : v.polynomialOrderBound (P i) + 2 * v.polynomialOrderBound (Q i) ≤ C := by
    dsimp only [C]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le
      (v.polynomialOrderBound (P j) + 2 * v.polynomialOrderBound (Q j))) (Finset.mem_univ i)
  have hle :
      (((v.polynomialOrderBound (P i) + 2 * v.polynomialOrderBound (Q i)) *
        (n + 1) : ℕ) : ℤ) ≤ ((C * (n + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_right (n + 1) hi
  exact (neg_le_neg hle).trans (hbound n)

/-- For the scalar rational function `q(T)=P(T)/Q(T)`, the formal translation
ratio minus one has zero constant term and a linear pole bound. Applying
this to an arbitrary curve still requires a constructed formal diagonal or
étale lift; rationality in a local parameter is not assumed here. -/
theorem translated_rational_difference_linear_pole_bound
    (P Q : Polynomial F) (t : F) (hP : P.eval t ≠ 0) (hQ : Q.eval t ≠ 0) :
    let T := Polynomial.C t + Polynomial.X
    let N := P.comp T * Polynomial.C (Q.eval t) - Q.comp T * Polynomial.C (P.eval t)
    let D := Q.comp T * Polynomial.C (P.eval t)
    let S := (N : PowerSeries F) * (D : PowerSeries F)⁻¹
    let C := v.polynomialOrderBound N + 2 * v.polynomialOrderBound D
    S = (P.comp T : PowerSeries F) * (Q.comp T : PowerSeries F)⁻¹ *
      PowerSeries.C (Q.eval t / P.eval t) - 1 ∧
      S * (D : PowerSeries F) = (N : PowerSeries F) ∧
      PowerSeries.constantCoeff S = 0 ∧
      ∀ n : ℕ, -((C * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n S) := by
  intro T N D S C
  have hP0 : (P.comp T).coeff 0 = P.eval t := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simp only [T, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero]
  have hQ0 : (Q.comp T).coeff 0 = Q.eval t := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simp only [T, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero]
  have hD : D.coeff 0 ≠ 0 := by
    change (Q.comp T * Polynomial.C (P.eval t)).coeff 0 ≠ 0
    rw [Polynomial.coeff_mul_C, hQ0]
    exact mul_ne_zero hQ hP
  have hN : N.coeff 0 = 0 := by
    change (P.comp T * Polynomial.C (Q.eval t) -
      Q.comp T * Polynomial.C (P.eval t)).coeff 0 = 0
    rw [Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C, hP0, hQ0]
    exact sub_eq_zero.mpr (mul_comm _ _)
  have hQseries : PowerSeries.constantCoeff (Q.comp T : PowerSeries F) ≠ 0 := by
    simpa only [Polynomial.constantCoeff_coe, hQ0] using hQ
  have hratio :
      (P.comp T : PowerSeries F) * (Q.comp T : PowerSeries F)⁻¹ *
        PowerSeries.C (Q.eval t / P.eval t) - 1 = S := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq (by
      simpa only [Polynomial.constantCoeff_coe] using hD)).mpr
    change ((P.comp T : PowerSeries F) * (Q.comp T : PowerSeries F)⁻¹ *
      PowerSeries.C (Q.eval t / P.eval t) - 1) *
        (Q.comp T * Polynomial.C (P.eval t) : Polynomial F) =
      (P.comp T * Polynomial.C (Q.eval t) -
        Q.comp T * Polynomial.C (P.eval t) : Polynomial F)
    simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C]
    calc
      _ = (P.comp T : PowerSeries F) *
          ((Q.comp T : PowerSeries F)⁻¹ * (Q.comp T : PowerSeries F)) *
          PowerSeries.C ((Q.eval t / P.eval t) * P.eval t) -
            (Q.comp T : PowerSeries F) * PowerSeries.C (P.eval t) := by
        rw [map_mul]
        ring
      _ = _ := by
        rw [PowerSeries.inv_mul_cancel _ hQseries, div_mul_cancel₀ _ hP, mul_one]
  obtain ⟨heq, hbound⟩ := polynomial_quotient_linear_pole_bound v N D hD
  refine ⟨hratio.symm, heq, ?_, hbound⟩
  change PowerSeries.constantCoeff ((N : PowerSeries F) * (D : PowerSeries F)⁻¹) = 0
  rw [map_mul, Polynomial.constantCoeff_coe, hN, zero_mul]

end AlgebraicCurve.Place
