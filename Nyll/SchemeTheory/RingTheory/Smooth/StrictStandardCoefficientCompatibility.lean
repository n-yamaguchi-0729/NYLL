/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.MatrixMinorScalarFactorization
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Coefficient compatibility for original strictly-standard data

Differentiate a relation modulo the square of the original relation ideal.
Its coefficient row annihilates the selected Jacobian modulo that ideal.
The actual matrix factorization supplied by the maximal minors then shows
that the strictly-standard parameter annihilates every coefficient modulo
the original ideal. No localization, basis choice, or Noetherian hypothesis
is needed.
-/

@[expose] public section

noncomputable section

universe u v w t

open scoped BigOperators

namespace Matrix

/-- A scalar in the maximal-minor ideal annihilates, modulo an ideal,
every coefficient of a row annihilating the rectangular matrix modulo
that ideal. The proof uses an actual scaled right inverse. -/
theorem mul_coeff_mem_of_row_mul_mem_of_mem_span_maximalMinors
    {S κ n : Type*} [CommRing S] [Fintype κ] [DecidableEq κ] [Finite n]
    (I : Ideal S) (A : Matrix κ n S) (d : S)
    (hd : d ∈ Ideal.span (Set.range fun a : κ → n =>
      (A.submatrix _root_.id a).det))
    (c : κ → S) (hc : ∀ j, (∑ i, c i * A i j) ∈ I) :
    ∀ i, d * c i ∈ I := by
  classical
  let _ : Fintype n := Fintype.ofFinite n
  obtain ⟨T, hT⟩ := exists_mul_eq_smul_one_of_mem_span_maximalMinors A d hd
  let V : Matrix Unit κ S := fun _ i => c i
  have hprod (i : κ) : ((V * A) * T) () i ∈ I := by
    change (∑ j, (∑ k, c k * A k j) * T j i) ∈ I
    exact I.sum_mem fun j _ => I.mul_mem_right _ (hc j)
  intro i
  have hi := hprod i
  rw [Matrix.mul_assoc, hT, Matrix.mul_smul, Matrix.mul_one] at hi
  exact hi

end Matrix

namespace MvPolynomial

variable {R n : Type*} [CommRing R]

/-- A partial derivative sends the square of any polynomial ideal into
that ideal. -/
theorem pderiv_mem_of_mem_square (I : Ideal (MvPolynomial n R))
    (x : MvPolynomial n R) (hx : x ∈ I ^ 2) (j : n) : pderiv j x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [pderiv_mul]
    exact I.add_mem (I.mul_mem_left _ hb) (I.mul_mem_right _ ha)
  · intro a b ha hb
    rw [map_add]
    exact I.add_mem ha hb

private theorem coeff_jacobian_mem_of_relation_mem_square
    {κ : Type*} [Fintype κ] (I : Ideal (MvPolynomial n R))
    (f : κ → MvPolynomial n R) (hf : ∀ i, f i ∈ I)
    (c : κ → MvPolynomial n R) (hc : (∑ i, c i * f i) ∈ I ^ 2) (j : n) :
    (∑ i, c i * pderiv j (f i)) ∈ I := by
  have hd := pderiv_mem_of_mem_square I (∑ i, c i * f i) hc j
  rw [map_sum] at hd
  simp only [pderiv_mul, Finset.sum_add_distrib] at hd
  have hleft : (∑ i, pderiv j (c i) * f i) ∈ I :=
    I.sum_mem fun i _ => I.mul_mem_left _ (hf i)
  exact (I.add_mem_iff_right hleft).mp hd

/-- If a selected relation combination belongs to the square of the
original ideal, a strictly-standard parameter multiplies each coefficient
into that original ideal. -/
theorem mul_coeff_mem_of_relation_mem_square
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Finite n]
    (I : Ideal (MvPolynomial n R)) (f : κ → MvPolynomial n R)
    (hf : ∀ i, f i ∈ I) (q : MvPolynomial n R)
    (hminor : q ∈ I ⊔ Ideal.span (Set.range fun a : κ → n =>
      ((Matrix.of fun i j => pderiv j (f i)).submatrix _root_.id a).det))
    (c : κ → MvPolynomial n R) (hc : (∑ i, c i * f i) ∈ I ^ 2) :
    ∀ i, q * c i ∈ I := by
  obtain ⟨u, hu, d, hd, hq⟩ := Submodule.mem_sup.mp hminor
  have hcoeff : ∀ i, d * c i ∈ I :=
    Matrix.mul_coeff_mem_of_row_mul_mem_of_mem_span_maximalMinors I
      (Matrix.of fun i j => pderiv j (f i)) d hd c
      (fun j => coeff_jacobian_mem_of_relation_mem_square I f hf c hc j)
  intro i
  rw [← hq, add_mul]
  exact I.add_mem (I.mul_mem_right _ hu) (hcoeff i)

end MvPolynomial

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- Coefficient compatibility in the actual original presentation:
a relation among the selected original relations modulo the square of
the kernel has every coefficient killed modulo the kernel by the
strictly-standard parameter. -/
theorem Presentation.mul_coeff_mem_ker_of_relation_mem_square
    {ι : Type w} {σ : Type t} {κ : Type*} [Finite ι]
    [Fintype κ] [DecidableEq κ] (P : Presentation R B ι σ)
    (a : κ → σ) (q : P.Ring)
    (hminor : q ∈ P.ker ⊔ Ideal.span (Set.range fun b : κ → ι =>
      ((Matrix.of fun i j => MvPolynomial.pderiv j (P.relation (a i))).submatrix
        _root_.id b).det))
    (c : κ → P.Ring)
    (hc : (∑ i, c i * P.relation (a i)) ∈ P.ker ^ 2) :
    ∀ i, q * c i ∈ P.ker :=
  MvPolynomial.mul_coeff_mem_of_relation_mem_square P.ker
    (fun i => P.relation (a i)) (fun i => P.relation_mem_ker (a i))
    q hminor c hc


/-- Two actual relation-coefficient systems satisfy exact compatibility
modulo the selected relation ideal after multiplication by the square of
the target strictly-standard parameter. The target system itself supplies
the exact generator inclusion; this inclusion is not an extra hypothesis. -/
theorem Presentation.sq_mul_crossCoefficient_mem_selected
    {ι : Type w} {σ : Type t} {κ : Type*} [Finite ι] [Fintype σ]
    [Fintype κ] [DecidableEq κ] (P : Presentation R B ι σ)
    (a : κ → σ) (qₛ qₜ : P.Ring)
    (hminor : qₜ ∈ P.ker ⊔ Ideal.span (Set.range fun b : κ → ι =>
      ((Matrix.of fun i j => MvPolynomial.pderiv j (P.relation (a i))).submatrix
        _root_.id b).det))
    (Hₛ : σ → σ → P.Ring) (Hₜ : σ → κ → P.Ring)
    (hₛ : ∀ j, qₛ * P.relation j = ∑ l, Hₛ j l * P.relation l)
    (hₜ : ∀ j, qₜ * P.relation j = ∑ i, Hₜ j i * P.relation (a i)) :
    ∀ j i, qₜ ^ 2 * (qₛ * Hₜ j i - ∑ l, Hₛ j l * Hₜ l i) ∈
      Ideal.span (Set.range fun k => P.relation (a k)) := by
  let J : Ideal P.Ring := Ideal.span (Set.range fun k => P.relation (a k))
  have htarget : ∀ x ∈ P.ker, qₜ * x ∈ J := by
    have hle : P.ker ≤ Submodule.comap (LinearMap.mulLeft P.Ring qₜ)
        (J : Submodule P.Ring P.Ring) := by
      conv_lhs => rw [← P.span_range_relation_eq_ker]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change qₜ * P.relation j ∈ J
      rw [hₜ j]
      exact J.sum_mem fun i _ => J.mul_mem_left _
        (Ideal.subset_span (Set.mem_range_self i))
    intro x hx
    exact hle hx
  intro j i
  let c : κ → P.Ring := fun k => qₛ * Hₜ j k - ∑ l, Hₛ j l * Hₜ l k
  have hzero : (∑ k, c k * P.relation (a k)) = 0 := by
    change (∑ k, (qₛ * Hₜ j k - ∑ l, Hₛ j l * Hₜ l k) * P.relation (a k)) = 0
    calc
      _ = qₛ * (∑ k, Hₜ j k * P.relation (a k)) -
          ∑ l, Hₛ j l * (∑ k, Hₜ l k * P.relation (a k)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
          Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
      _ = qₛ * (qₜ * P.relation j) - ∑ l, Hₛ j l * (qₜ * P.relation l) := by
        simp only [← hₜ]
      _ = qₜ * (qₛ * P.relation j - ∑ l, Hₛ j l * P.relation l) := by
        simp only [mul_sub, Finset.mul_sum, mul_left_comm]
      _ = 0 := by rw [hₛ j, sub_self, mul_zero]
  have hc : (∑ k, c k * P.relation (a k)) ∈ P.ker ^ 2 := by
    rw [hzero]
    exact (P.ker ^ 2).zero_mem
  have hcoeff : qₜ * c i ∈ P.ker :=
    P.mul_coeff_mem_ker_of_relation_mem_square a qₜ hminor c hc i
  have hcompat := htarget (qₜ * c i) hcoeff
  simpa only [c, pow_two, mul_assoc] using hcompat

end Algebra
