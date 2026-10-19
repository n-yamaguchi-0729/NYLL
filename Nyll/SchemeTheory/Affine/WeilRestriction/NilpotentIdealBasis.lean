/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionSplitting
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Coordinates adapted to the actual ideal of a finite algebra -/

noncomputable section

universe u

open Module

namespace SchemeTheory.Affine.UnitNormPolynomial

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
  (I : Ideal A)

/-- The actual ideal and quotient bases extend to a basis of the finite algebra.
The first block has exactly the dimension of the given ideal. -/
theorem exists_idealSplitBasis :
    ∃ bA : Basis
      (Fin (Module.finrank K I) ⊕ Fin (Module.finrank K (A ⧸ I))) K A,
      (∀ i, Ideal.Quotient.mkₐ K I (bA (Sum.inl i)) = 0) ∧
      (∀ j, Ideal.Quotient.mkₐ K I (bA (Sum.inr j)) = Module.finBasis K (A ⧸ I) j) := by
  let p := (Ideal.Quotient.mkₐ K I).toLinearMap
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective K I))
  have hps (b : A ⧸ I) : p (s b) = b := LinearMap.congr_fun hs b
  let L : I × (A ⧸ I) →ₗ[K] A := (I.restrictScalars K).subtype.coprod s
  have hL (z : I × (A ⧸ I)) : p (L z) = z.2 := by
    change p ((z.1 : A) + s z.2) = z.2
    rw [map_add, hps]
    have hz : p (z.1 : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr z.1.property
    rw [hz, zero_add]
  have hinj : Function.Injective L := by
    intro x y h
    have h₂ : x.2 = y.2 := (hL x).symm.trans ((congrArg p h).trans (hL y))
    apply Prod.ext
    · apply Subtype.ext
      change (x.1 : A) + s x.2 = (y.1 : A) + s y.2 at h
      rw [h₂] at h
      exact add_right_cancel h
    · exact h₂
  have hsurj : Function.Surjective L := by
    intro a
    have hk : a - s (p a) ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change p (a - s (p a)) = 0
      rw [map_sub, hps, sub_self]
    refine ⟨(⟨a - s (p a), hk⟩, p a), ?_⟩
    change a - s (p a) + s (p a) = a
    exact sub_add_cancel _ _
  let e : (I × (A ⧸ I)) ≃ₗ[K] A := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  refine ⟨((Module.finBasis K I).prod (Module.finBasis K (A ⧸ I))).map e, ?_, ?_⟩
  · intro i
    rw [Basis.map_apply]
    change p (L (((Module.finBasis K I).prod (Module.finBasis K (A ⧸ I))) (Sum.inl i))) = 0
    rw [hL, Basis.prod_apply_inl_snd]
  · intro j
    rw [Basis.map_apply]
    change p (L (((Module.finBasis K I).prod (Module.finBasis K (A ⧸ I))) (Sum.inr j))) = _
    rw [hL, Basis.prod_apply_inr_snd]

/-- A chosen adapted basis, constructed from the original ideal. -/
def idealSplitBasis : Basis
    (Fin (Module.finrank K I) ⊕ Fin (Module.finrank K (A ⧸ I))) K A :=
  (exists_idealSplitBasis (K := K) I).choose

/-- The ideal block is killed by the original quotient morphism. -/
theorem idealSplitBasis_left (i : Fin (Module.finrank K I)) :
    Ideal.Quotient.mkₐ K I (idealSplitBasis I (Sum.inl i)) = 0 :=
  (exists_idealSplitBasis (K := K) I).choose_spec.1 i

/-- The quotient block maps to the original quotient basis. -/
theorem idealSplitBasis_right (j : Fin (Module.finrank K (A ⧸ I))) :
    Ideal.Quotient.mkₐ K I (idealSplitBasis I (Sum.inr j)) = Module.finBasis K (A ⧸ I) j :=
  (exists_idealSplitBasis (K := K) I).choose_spec.2 j

end SchemeTheory.Affine.UnitNormPolynomial
