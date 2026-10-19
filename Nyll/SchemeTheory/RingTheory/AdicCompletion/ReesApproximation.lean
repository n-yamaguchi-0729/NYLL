/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Tactic.Choose

/-!
# Finite approximation from the residual Rees algebra

Suppose `I` is finitely generated and `R/I` is Noetherian. The quotient of
the Rees algebra by its extended coefficient ideal is of finite type over
`R/I`, hence Noetherian. For every ideal `J`, finitely many homogeneous
initial forms therefore control all its adic orders.

The construction below selects actual elements of `J` and proves a uniform
bound on the orders of coefficients needed to improve an approximation by
one degree. No Noetherianity of `R` or closedness of `J` is assumed. This is
the algebraic part of the proof of Stacks, Tag 05GH.
-/

noncomputable section

open Polynomial

universe u

namespace AdicCompletion

namespace NoetherianCriterion

variable {R : Type u} [CommRing R] (I : Ideal R)

private def reesMonomial (n : ℕ) (x : R) (hx : x ∈ I ^ n) : reesAlgebra I :=
  ⟨Polynomial.monomial n x, reesAlgebra.monomial_mem.mpr hx⟩

/-- Multiplication by the coefficient ideal raises every Rees coefficient
by one adic order. -/
private theorem coeff_mem_pow_succ_of_mem_map
    (f : reesAlgebra I) (hf : f ∈ I.map (algebraMap R (reesAlgebra I))) (n : ℕ) :
    (f : R[X]).coeff n ∈ I ^ (n + 1) := by
  have hf' : f ∈ I • (⊤ : Submodule R (reesAlgebra I)) := by
    rw [Ideal.smul_top_eq_map]
    exact hf
  refine Submodule.smul_induction_on hf' ?_ ?_
  · intro r hr g _
    rw [Subalgebra.coe_smul, Polynomial.coeff_smul, smul_eq_mul, pow_succ']
    exact Ideal.mul_mem_mul hr (g.property n)
  · intro f g hf hg
    change ((f : R[X]) + (g : R[X])).coeff n ∈ I ^ (n + 1)
    rw [Polynomial.coeff_add]
    exact Ideal.add_mem _ hf hg

/-- A finitely generated coefficient ideal and a Noetherian quotient make
the residual Rees algebra Noetherian, without assuming the original ring
is Noetherian. -/
theorem residualRees_isNoetherianRing (hI : I.FG) [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
  let S := reesAlgebra I
  let K : Ideal S := I.map (algebraMap R S)
  let G := S ⧸ K
  have : Algebra.FiniteType R S := ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  have : Algebra.FiniteType R G :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R K) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (R ⧸ I) G :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) G
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I) G

/-- Finitely many actual elements of any ideal improve every adic
approximation. The coefficient bound depends only on the chosen family,
and is uniform over all elements and adic orders. -/
theorem exists_finite_approximation (hI : I.FG) [IsNoetherianRing (R ⧸ I)] (J : Ideal R) :
    ∃ (r : ℕ) (g : Fin r → R) (c : ℕ),
      (∀ i, g i ∈ J) ∧
      ∀ (n : ℕ) (x : R), x ∈ J → x ∈ I ^ n →
        ∃ a : Fin r → R, (∀ i, a i ∈ I ^ (n - c)) ∧
          x - ∑ i, a i * g i ∈ I ^ (n + 1) := by
  classical
  let S := reesAlgebra I
  let K : Ideal S := I.map (algebraMap R S)
  let G := S ⧸ K
  let q : S →+* G := Ideal.Quotient.mk K
  have : IsNoetherianRing G := residualRees_isNoetherianRing I hI
  let T : Set G := {z | ∃ (d : ℕ) (x : R) (_ : x ∈ J) (hx : x ∈ I ^ d),
    q (reesMonomial I d x hx) = z}
  let L : Ideal G := Ideal.span T
  obtain ⟨s, hsT, hsgen⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset T).mp (IsNoetherian.noetherian L)
  let r := Fintype.card s
  let e : Fin r ≃ s := (Fintype.equivFin s).symm
  let z : Fin r → G := fun i => (e i).val
  have hz : Set.range z = (s : Set G) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hy
      obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hspan : Ideal.span (Set.range z) = L := by
    rw [hz]
    exact hsgen.symm
  have hchoose : ∀ i : Fin r,
      ∃ (d : ℕ) (x : R) (_ : x ∈ J) (hx : x ∈ I ^ d),
        q (reesMonomial I d x hx) = z i := by
    intro i
    exact hsT (e i).property
  choose d g hgJ hgI hgq using hchoose
  let c : ℕ := Finset.univ.sup d
  have hd : ∀ i, d i ≤ c := fun i => Finset.le_sup (Finset.mem_univ i)
  refine ⟨r, g, c, hgJ, ?_⟩
  intro n x hxJ hxI
  have hxspan : q (reesMonomial I n x hxI) ∈ Ideal.span (Set.range z) := by
    rw [hspan]
    exact Ideal.subset_span ⟨n, x, hxJ, hxI, rfl⟩
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hxspan
  choose p hp using fun i : Fin r => Ideal.Quotient.mk_surjective (a i)
  have hpq : ∀ i : Fin r, q (p i) = a i := fun i => hp i
  let F : S := reesMonomial I n x hxI - ∑ i, p i * reesMonomial I (d i) (g i) (hgI i)
  have hF : F ∈ K := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change q F = 0
    simp only [F, map_sub, map_sum, map_mul, hpq, hgq, ha, sub_self]
  let a' : Fin r → R := fun i => if d i ≤ n then (p i : R[X]).coeff (n - d i) else 0
  have ha' : ∀ i, a' i ∈ I ^ (n - c) := by
    intro i
    by_cases hi : d i ≤ n
    · change (if d i ≤ n then (p i : R[X]).coeff (n - d i) else 0) ∈ I ^ (n - c)
      rw [ite_eq_left hi]
      exact Ideal.pow_le_pow_right (Nat.sub_le_sub_left (hd i) n) ((p i).property (n - d i))
    · change (if d i ≤ n then (p i : R[X]).coeff (n - d i) else 0) ∈ I ^ (n - c)
      rw [ite_eq_right hi]
      exact Ideal.zero_mem _
  have hcoeff : (F : R[X]).coeff n = x - ∑ i, a' i * g i := by
    let v : S →+* R[X] := (reesAlgebra I).val.toRingHom
    change (v F).coeff n = x - ∑ i, a' i * g i
    dsimp only [F]
    rw [map_sub, map_sum, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
    change (Polynomial.monomial n x).coeff n -
      ∑ i, (v (p i * reesMonomial I (d i) (g i) (hgI i))).coeff n = _
    rw [Polynomial.coeff_monomial, ite_eq_left rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
    change ((p i : R[X]) * Polynomial.monomial (d i) (g i)).coeff n = a' i * g i
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, Polynomial.coeff_mul_X_pow']
    by_cases hi : d i ≤ n
    · rw [ite_eq_left hi, Polynomial.coeff_mul_C]
      change (p i : R[X]).coeff (n - d i) * g i =
        (if d i ≤ n then (p i : R[X]).coeff (n - d i) else 0) * g i
      rw [ite_eq_left hi]
    · rw [ite_eq_right hi]
      change 0 = (if d i ≤ n then (p i : R[X]).coeff (n - d i) else 0) * g i
      rw [ite_eq_right hi, zero_mul]
  refine ⟨a', ha', ?_⟩
  rw [← hcoeff]
  exact coeff_mem_pow_succ_of_mem_map I F hF n

end NoetherianCriterion

end AdicCompletion
