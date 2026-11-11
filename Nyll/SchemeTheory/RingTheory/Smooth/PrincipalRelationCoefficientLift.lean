/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Lifting the actual relation coefficients from a principal quotient

Exact relation-ideal membership over `R/(π²)` gives original polynomial
coefficients and an actual `π²` remainder. These are the syzygies used by
the principal lifting algebra, rather than additional supplied identities.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {R n m κ : Type*} [CommRing R] [Fintype κ]

/-- Exact selected-relation memberships over the principal quotient lift
to actual polynomial identities over the original base. -/
theorem exists_lift_principal_relation_coefficients
    (π : R) (f : m → MvPolynomial n R) (a : κ → m)
    (qbar : MvPolynomial n (R ⧸ Ideal.span {π ^ 2}))
    (hrel : ∀ j, qbar * map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) ∈
      Ideal.span (Set.range fun i =>
        map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f (a i)))) :
    ∃ (q : MvPolynomial n R) (h : m → κ → MvPolynomial n R)
      (g : m → MvPolynomial n R),
      map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) q = qbar ∧
      ∀ j, q * f j = ∑ i, h j i * f (a i) + C (π ^ 2) * g j := by
  classical
  let Q := R ⧸ Ideal.span {π ^ 2}
  let ρ : R →+* Q := Ideal.Quotient.mk (Ideal.span {π ^ 2})
  have hsur : Function.Surjective (map (σ := n) ρ) :=
    map_surjective ρ Ideal.Quotient.mk_surjective
  obtain ⟨q, hq⟩ := hsur qbar
  have hcoeff (j : m) : ∃ c : κ → MvPolynomial n Q,
      qbar * map ρ (f j) = ∑ i, c i * map ρ (f (a i)) := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hrel j)
    exact ⟨c, hc.symm⟩
  choose c hc using hcoeff
  have hcoeffLift (j : m) (i : κ) : ∃ p : MvPolynomial n R, map ρ p = c j i :=
    hsur (c j i)
  choose h hh using hcoeffLift
  have hrem (j : m) : ∃ g : MvPolynomial n R,
      q * f j = ∑ i, h j i * f (a i) + C (π ^ 2) * g := by
    have hzero : map ρ (q * f j - ∑ i, h j i * f (a i)) = 0 := by
      rw [map_sub, map_mul, hq, map_sum]
      simp only [map_mul, hh]
      exact sub_eq_zero.mpr (hc j)
    have hdiv : C (π ^ 2) ∣ q * f j - ∑ i, h j i * f (a i) := by
      apply (C_dvd_iff_map_hom_eq_zero ρ (π ^ 2) (fun r => ?_) _).mpr hzero
      change Ideal.Quotient.mk (Ideal.span {π ^ 2}) r = 0 ↔ π ^ 2 ∣ r
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    obtain ⟨g, hg⟩ := hdiv
    exact ⟨g, sub_eq_iff_eq_add.mp hg |>.trans (add_comm _ _)⟩
  choose g hg using hrem
  exact ⟨q, h, g, hq, hg⟩

/-- For selected relations, choose the literal diagonal coefficients and
zero remainder. This normalization is constructed, not added as a condition
on the quotient relation data. -/
theorem exists_normalized_lift_principal_relation_coefficients [DecidableEq κ]
    (π : R) (f : m → MvPolynomial n R) (a : κ → m) (ha : Function.Injective a)
    (qbar : MvPolynomial n (R ⧸ Ideal.span {π ^ 2}))
    (hrel : ∀ j, qbar * map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) ∈
      Ideal.span (Set.range fun i =>
        map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f (a i)))) :
    ∃ (q : MvPolynomial n R) (h : m → κ → MvPolynomial n R)
      (g : m → MvPolynomial n R),
      map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) q = qbar ∧
      (∀ j, q * f j = ∑ i, h j i * f (a i) + C (π ^ 2) * g j) ∧
      (∀ i j, h (a i) j = if j = i then q else 0) ∧ ∀ i, g (a i) = 0 := by
  obtain ⟨q, h, g, hq, hg⟩ := exists_lift_principal_relation_coefficients π f a qbar hrel
  let h' := Function.extend a (fun i j => if j = i then q else 0) h
  let g' := Function.extend a (fun _ : κ => (0 : MvPolynomial n R)) g
  refine ⟨q, h', g', hq, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : ∃ i, a i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [show h' (a i) = (fun j => if j = i then q else 0) from ha.extend_apply _ _ i,
        show g' (a i) = 0 from ha.extend_apply _ _ i, mul_zero, add_zero]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · rw [show h' j = h j from Function.extend_apply' _ _ _ hj,
        show g' j = g j from Function.extend_apply' _ _ _ hj]
      exact hg j
  · intro i j
    exact congrFun (ha.extend_apply (fun i j => if j = i then q else 0) h i) j
  · intro i
    exact ha.extend_apply _ _ i

omit [Fintype κ] in
/-- Insert the selected coefficients into the full original relation
indexing. The new matrix has zero columns off the selected set and literal
diagonal rows on that set, as required by the lifting charts. -/
theorem exists_full_normalized_lift_principal_relation_coefficients
    [Finite κ] [Fintype m] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (a : κ → m) (ha : Function.Injective a)
    (qbar : MvPolynomial n (R ⧸ Ideal.span {π ^ 2}))
    (hrel : ∀ j, qbar * map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) ∈
      Ideal.span (Set.range fun i =>
        map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f (a i)))) :
    ∃ (q : MvPolynomial n R) (H : m → m → MvPolynomial n R)
      (g : m → MvPolynomial n R),
      map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) q = qbar ∧
      (∀ j, q * f j = ∑ l, H j l * f l + C (π ^ 2) * g j) ∧
      (∀ i l, H (a i) l = if l = a i then q else 0) ∧
      (∀ j l, l ∉ Set.range a → H j l = 0) ∧ ∀ i, g (a i) = 0 := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  obtain ⟨q, h, g, hq, hg, hh, hzero⟩ :=
    exists_normalized_lift_principal_relation_coefficients π f a ha qbar hrel
  let H : m → m → MvPolynomial n R := fun j l => ∑ i, if a i = l then h j i else 0
  have hsum (j : m) : (∑ l, H j l * f l) = ∑ i, h j i * f (a i) := by
    dsimp only [H]
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine ⟨q, H, g, hq, ?_, ?_, ?_, hzero⟩
  · intro j
    rw [hsum]
    exact hg j
  · intro i l
    dsimp only [H]
    simp only [hh]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
      by_cases hli : a i = l
      · rw [ite_eq_left hli, ite_eq_left hli.symm]
      · rw [ite_eq_right hli, ite_eq_right (Ne.symm hli)]
    · intro j _ hji
      rw [ite_eq_right hji]
      exact ite_self 0
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · intro j l hl
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hai => hl ⟨i, hai⟩)

end MvPolynomial
