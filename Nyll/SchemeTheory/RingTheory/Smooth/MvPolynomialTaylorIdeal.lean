/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The multivariate Taylor remainder in a squared ideal

If the increments of finitely many polynomial variables lie in an
ideal, the error after the linear Taylor term lies in its square.
The proof uses the existing partial derivatives and the equality of
evaluation maps after quotienting by the ideal.

For increments divisible by the square of a base element, this gives
the fourth-order remainder used in the desingularization calculation
of Stacks Project, Lemma 16.7.1:
https://stacks.math.columbia.edu/tag/07CR
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

/-- The first-order Taylor remainder belongs to the square of any
ideal containing the variable increments. -/
theorem aeval_add_sub_linear_mem_ideal_sq
    {R B σ : Type*} [CommRing R] [CommRing B] [Algebra R B] [Fintype σ]
    (I : Ideal B) (x d : σ → B) (hd : ∀ i, d i ∈ I)
    (p : MvPolynomial σ R) :
    aeval (fun i => x i + d i) p - aeval x p -
      ∑ i, aeval x (pderiv i p) * d i ∈ I ^ 2 := by
  classical
  let e₀ : MvPolynomial σ R →ₐ[R] B := aeval x
  let e₁ : MvPolynomial σ R →ₐ[R] B := aeval (fun i => x i + d i)
  let q : B →ₐ[R] B ⧸ I := Ideal.Quotient.mkₐ R I
  have he₀X (i : σ) : e₀ (X i) = x i := aeval_X x i
  have he₁X (i : σ) : e₁ (X i) = x i + d i :=
    aeval_X (fun j => x j + d j) i
  have he₀C (r : R) : e₀ (C r) = algebraMap R B r := aeval_C x r
  have he₁C (r : R) : e₁ (C r) = algebraMap R B r :=
    aeval_C (fun j => x j + d j) r
  have hq : q.comp e₁ = q.comp e₀ := by
    apply MvPolynomial.algHom_ext
    intro i
    change q (aeval (fun j => x j + d j) (X i)) = q (aeval x (X i))
    rw [aeval_X, aeval_X, map_add,
      show q (d i) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (hd i), add_zero]
  have hdiff (f : MvPolynomial σ R) : e₁ f - e₀ f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (e₁ f - e₀ f) = 0
    rw [map_sub]
    have h := AlgHom.congr_fun hq f
    change q (e₁ f) = q (e₀ f) at h
    rw [h, sub_self]
  let lin : MvPolynomial σ R → B := fun f => ∑ i, e₀ (pderiv i f) * d i
  have hlinC (r : R) : lin (C r) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    rw [pderiv_C, map_zero, zero_mul]
  have hlinadd (f g : MvPolynomial σ R) : lin (f + g) = lin f + lin g := by
    change (∑ i, e₀ (pderiv i (f + g)) * d i) =
      (∑ i, e₀ (pderiv i f) * d i) + ∑ i, e₀ (pderiv i g) * d i
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  have hlinmulX (f : MvPolynomial σ R) (j : σ) :
      lin (f * X j) = lin f * x j + e₀ f * d j := by
    have hsum :
        (∑ i, e₀ (pderiv i (f * X j)) * d i) =
          (∑ i, (e₀ (pderiv i f) * d i) * x j) +
            ∑ i, e₀ f * e₀ (pderiv i (X j)) * d i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [pderiv_mul, map_add]
      simp only [map_mul]
      rw [he₀X]
      ring
    have hsingle :
        (∑ i, e₀ f * e₀ (pderiv i (X j)) * d i) = e₀ f * d j := by
      rw [Finset.sum_eq_single j]
      · rw [pderiv_X_self, map_one, mul_one]
      · intro i _hi hij
        rw [pderiv_X_of_ne (Ne.symm hij), map_zero, mul_zero, zero_mul]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
    change (∑ i, e₀ (pderiv i (f * X j)) * d i) = lin f * x j + e₀ f * d j
    rw [hsum, hsingle, ← Finset.sum_mul]
  change e₁ p - e₀ p - lin p ∈ I ^ 2
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [hlinC, he₁C, he₀C, sub_self, sub_zero]
    exact Ideal.zero_mem _
  | add f g hf hg =>
    rw [map_add, map_add, hlinadd]
    have heq : e₁ f + e₁ g - (e₀ f + e₀ g) - (lin f + lin g) =
        (e₁ f - e₀ f - lin f) + (e₁ g - e₀ g - lin g) := by ring
    rw [heq]
    exact Ideal.add_mem _ hf hg
  | mul_X f j hf =>
    rw [map_mul, map_mul, hlinmulX, he₁X, he₀X]
    have heq : e₁ f * (x j + d j) - e₀ f * x j -
        (lin f * x j + e₀ f * d j) =
          (e₁ f - e₀ f - lin f) * x j + (e₁ f - e₀ f) * d j := by ring
    rw [heq]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ hf
    · rw [pow_two]
      exact Ideal.mul_mem_mul (hdiff f) (hd j)

end MvPolynomial
