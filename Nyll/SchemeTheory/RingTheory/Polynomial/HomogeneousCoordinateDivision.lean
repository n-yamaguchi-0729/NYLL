/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Dividing a homogeneous polynomial by a coordinate power

Cross multiplication with two distinct coordinates forces divisibility
by a coordinate power over any commutative coefficient semiring. This
is a coefficient calculation, so no domain assumption is needed. The
actual monomial quotient is homogeneous of the expected degree. The
one-variable version supplies the same division for projective zero-space.
-/

noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- If two distinct coordinate powers cross multiply, the polynomial on
the opposite side is divisible by the first coordinate power. -/
theorem X_pow_dvd_of_cross_mul {i j : σ} (hij : i ≠ j) (k : ℕ)
    {p q : MvPolynomial σ R}
    (h : X i ^ k * q = X j ^ k * p) : X i ^ k ∣ p := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  apply MvPolynomial.ext
  intro e
  rw [AddMonoidAlgebra.coeff_zero]
  by_cases he : Finsupp.single i k ≤ e
  · exact coeff_modMonomial_of_le p he
  · rw [coeff_modMonomial_of_not_le p he]
    have he' : ¬Finsupp.single i k ≤ Finsupp.single j k + e := by
      intro he'
      apply he
      rw [Finsupp.single_le_iff] at he' ⊢
      simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij, zero_add] using he'
    have hc := congrArg (fun f : MvPolynomial σ R =>
      f.coeff (Finsupp.single j k + e)) h
    rw [X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul',
      ite_eq_right he', coeff_monomial_mul, one_mul] at hc
    exact hc.symm

/-- Removing a coordinate monomial lowers the homogeneous degree by its
exponent, even when the remainder is nonzero. -/
theorem IsHomogeneous.divMonomial_single {p : MvPolynomial σ R} {d k : ℕ}
    (hp : p.IsHomogeneous (d + k)) (i : σ) :
    (p.divMonomial (Finsupp.single i k)).IsHomogeneous d := by
  intro e he
  have hdeg := hp (show p.coeff (Finsupp.single i k + e) ≠ 0 from he)
  change (Finsupp.weight (fun _ : σ => 1)) (Finsupp.single i k + e) = d + k at hdeg
  change (Finsupp.weight (fun _ : σ => 1)) e = d
  rw [← Finsupp.degree_eq_weight_one] at hdeg ⊢
  rw [map_add, Finsupp.degree_single] at hdeg
  exact Nat.add_left_cancel (hdeg.trans (Nat.add_comm d k))

/-- The canonical monomial quotient recovers a polynomial known to be
divisible by the specified coordinate power. -/
theorem X_pow_mul_divMonomial_single {p : MvPolynomial σ R} (i : σ) (k : ℕ)
    (hp : X i ^ k ∣ p) : X i ^ k * p.divMonomial (Finsupp.single i k) = p := by
  have hrem : p.modMonomial (Finsupp.single i k) = 0 := by
    apply monomial_one_dvd_iff_modMonomial_eq_zero.mp
    simpa only [← X_pow_eq_monomial] using hp
  have h := divMonomial_add_modMonomial p (Finsupp.single i k)
  rw [← X_pow_eq_monomial, hrem, add_zero] at h
  exact h

/-- In one variable, homogeneity alone supplies divisibility by every
coordinate power at most the degree. -/
theorem IsHomogeneous.X_pow_dvd_of_subsingleton [Subsingleton σ]
    {p : MvPolynomial σ R} {d k : ℕ} (hp : p.IsHomogeneous (d + k)) (i : σ) :
    X i ^ k ∣ p := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  apply MvPolynomial.ext
  intro e
  rw [AddMonoidAlgebra.coeff_zero]
  by_cases he : Finsupp.single i k ≤ e
  · exact coeff_modMonomial_of_le p he
  · rw [coeff_modMonomial_of_not_le p he]
    by_contra hc
    have hdeg := hp hc
    change (Finsupp.weight (fun _ : σ => 1)) e = d + k at hdeg
    rw [← Finsupp.degree_eq_weight_one] at hdeg
    have heq : e = Finsupp.single i (e i) := by
      apply Finsupp.ext
      intro j
      have hji : j = i := Subsingleton.elim j i
      rw [hji, Finsupp.single_eq_same]
    have hdeg' : e i = d + k := by
      rw [heq, Finsupp.degree_single] at hdeg
      exact hdeg
    apply he
    rw [Finsupp.single_le_iff, hdeg']
    exact Nat.le_add_left k d

end MvPolynomial
