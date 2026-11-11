/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingChartSyzygyDivisibility

/-!
# The original source quotient in principal lifting

The lifted polynomial presentation modulo `π` is canonically isomorphic
to the original algebra modulo the image of `π`. The kernel calculation
uses the original presentation and coefficient reduction modulo `π²`.
The resulting ring equivalence preserves every polynomial representative
and requires no additional algebra structure on either quotient.
-/

@[expose] public section

noncomputable section

namespace Algebra

open MvPolynomial

/-- Reducing the lifted original relations modulo `π` gives exactly the
original presented algebra modulo its image of `π`. The equivalence retains
the original polynomial evaluation map, on every representative. -/
theorem Presentation.exists_principal_lifting_original_quotient_equiv
    {R B n m : Type*} [CommRing R] (π : R) [CommRing B]
    [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hf : ∀ j, map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) = P.relation j) :
    let bπ := algebraMap (R ⧸ Ideal.span {π ^ 2}) B
      (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)
    ∃ e : (MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span {C π})) ≃+* B ⧸ Ideal.span {bπ},
      ∀ p : MvPolynomial n R,
        e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk (Ideal.span {bπ})
          (algebraMap P.Ring B
            (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) p)) := by
  intro bπ
  let ρ : R →+* R ⧸ Ideal.span {π ^ 2} := Ideal.Quotient.mk (Ideal.span {π ^ 2})
  let δ : MvPolynomial n R →+* B := (algebraMap P.Ring B).comp (map ρ)
  have hδ : Function.Surjective δ :=
    P.algebraMap_surjective.comp (map_surjective ρ Ideal.Quotient.mk_surjective)
  have hδπ : δ (C π) = bπ := by
    change algebraMap P.Ring B (map ρ (C π)) = bπ
    rw [map_C, P.algebraMap_apply, aeval_C]
  have hδf (j : m) : δ (f j) = 0 := by
    change algebraMap P.Ring B (map ρ (f j)) = 0
    rw [hf j]
    exact P.relation_mem_ker j
  let τ : B →+* B ⧸ Ideal.span {bπ} := Ideal.Quotient.mk (Ideal.span {bπ})
  let ψ : MvPolynomial n R →+* B ⧸ Ideal.span {bπ} := τ.comp δ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hδ
  let J : Ideal (MvPolynomial n R) := Ideal.span (Set.range f) ⊔ Ideal.span {C π}
  have hJ : J ≤ RingHom.ker ψ := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change τ (δ (f j)) = 0
      rw [hδf j, map_zero]
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      change τ (δ (C π)) = 0
      rw [hδπ]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton _))
  have hsquare : Ideal.span {(C (π ^ 2) : MvPolynomial n R)} ≤ J := by
    apply le_trans _ (show Ideal.span {C π} ≤ J from le_sup_right)
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [map_pow, pow_two]
    exact (Ideal.span {(C π : MvPolynomial n R)}).mul_mem_left _
      (Ideal.subset_span (Set.mem_singleton _))
  have hker : RingHom.ker ψ = J := by
    apply le_antisymm _ hJ
    intro x hx
    have hx' : δ x ∈ Ideal.span {bπ} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (show τ (δ x) = 0 from hx)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx'
    obtain ⟨y, hy⟩ := hδ b
    have hsub : map ρ (x - C π * y) ∈ P.ker := by
      change δ (x - C π * y) = 0
      rw [map_sub, map_mul, hδπ, hy, hb, sub_self]
    have hmap : map ρ (x - C π * y) ∈
        Ideal.span (Set.range fun j => map ρ (f j)) := by
      have heq : (fun j => map ρ (f j)) = P.relation := funext hf
      rw [heq, P.span_range_relation_eq_ker]
      exact hsub
    have hrem : x - C π * y ∈ J :=
      (show Ideal.span (Set.range f) ⊔ Ideal.span {C (π ^ 2)} ≤ J from
        sup_le le_sup_left hsquare)
        (mem_selected_sup_principalSquare_of_map_mem π f (x - C π * y) hmap)
    have hprod : C π * y ∈ J :=
      J.mul_mem_right y ((show Ideal.span {C π} ≤ J from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _)))
    simpa only [sub_add_cancel] using J.add_mem hrem hprod
  let e : (MvPolynomial n R ⧸ J) ≃+* B ⧸ Ideal.span {bπ} :=
    (Ideal.quotEquivOfEq hker.symm).trans (ψ.quotientKerEquivOfSurjective hψ)
  refine ⟨e, ?_⟩
  intro p
  change ψ.quotientKerEquivOfSurjective hψ
      (Ideal.quotEquivOfEq hker.symm (Ideal.Quotient.mk J p)) =
    Ideal.Quotient.mk (Ideal.span {bπ}) (algebraMap P.Ring B (map ρ p))
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

end Algebra
