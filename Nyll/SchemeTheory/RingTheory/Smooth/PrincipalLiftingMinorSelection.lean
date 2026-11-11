/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.StrictStandardPresentationBaseChange
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Selecting an original Jacobian minor in a principal lifting chart

A strictly-standard parameter outside an ideal containing the original
relations and the square parameter supplies a Jacobian minor outside that
same ideal. The minor uses distinct original variables. All coefficient
reduction and kernel comparisons are proved for the actual presentation.
-/

@[expose] public section

namespace MvPolynomial

/-- Quotient strictly-standard data select an actual original minor outside
the specified ideal. No chosen minor or variable injection is assumed. -/
theorem exists_original_jacobianMinor_notMem_of_principal_quotient
    {R n m κ B : Type*} [CommRing R] [CommRing B]
    [Fintype κ] [DecidableEq κ] (π : R)
    [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Algebra.Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hP : ∀ j, P.relation j = map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j))
    (a : κ → m) (q : MvPolynomial n R) (p : Ideal (MvPolynomial n R))
    (hπ : C (π ^ 2) ∈ p) (hf : ∀ j, f j ∈ p) (hq : q ∉ p)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) q ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det)) :
    ∃ b : κ → n, Function.Injective b ∧
      ((Matrix.of fun i j => pderiv j (f (a i))).submatrix _root_.id b).det ∉ p := by
  classical
  let ρ : R →+* R ⧸ Ideal.span {π ^ 2} := Ideal.Quotient.mk (Ideal.span {π ^ 2})
  let μ : MvPolynomial n R →+* MvPolynomial n (R ⧸ Ideal.span {π ^ 2}) := map ρ
  have hsur : Function.Surjective μ := map_surjective ρ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker μ ≤ p := by
    intro x hx
    have hx' : map ρ x = 0 := hx
    have hdiv : C (π ^ 2) ∣ x := by
      apply (C_dvd_iff_map_hom_eq_zero ρ (π ^ 2) (fun r => ?_) _).mpr hx'
      change Ideal.Quotient.mk (Ideal.span {π ^ 2}) r = 0 ↔ π ^ 2 ∣ r
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    obtain ⟨y, rfl⟩ := hdiv
    exact p.mul_mem_right _ hπ
  have hqbar : μ q ∉ p.map μ := by
    intro hmem
    have hpre : q ∈ (p.map μ).comap μ := hmem
    rw [Ideal.comap_map_of_surjective μ hsur p] at hpre
    exact hq ((sup_le le_rfl hker) hpre)
  have hrelations : P.ker ≤ p.map μ := by
    rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [hP]
    exact Ideal.mem_map_of_mem μ (hf j)
  have hex : ∃ b : κ → n,
      ((Matrix.of fun i j => pderiv j (f (a i))).submatrix _root_.id b).det ∉ p := by
    by_contra hn
    have hall (b : κ → n) :
        ((Matrix.of fun i j => pderiv j (f (a i))).submatrix _root_.id b).det ∈ p := by
      by_contra hb
      exact hn ⟨b, hb⟩
    have hminors : Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det) ≤
          p.map μ := by
      apply Ideal.span_le.mpr
      rintro _ ⟨b, rfl⟩
      simp only [hP]
      rw [← map_jacobianMinor ρ (fun i => f (a i)) b]
      exact Ideal.mem_map_of_mem μ (hall b)
    exact hqbar ((sup_le hrelations hminors) hminor)
  obtain ⟨b, hb⟩ := hex
  refine ⟨b, ?_, hb⟩
  intro i j hij
  by_contra hne
  have hzero :
      ((Matrix.of fun i j => pderiv j (f (a i))).submatrix _root_.id b).det = 0 := by
    apply Matrix.det_zero_of_column_eq hne
    intro l
    change pderiv (b i) (f (a l)) = pderiv (b j) (f (a l))
    rw [hij]
  apply hb
  rw [hzero]
  exact p.zero_mem

end MvPolynomial
