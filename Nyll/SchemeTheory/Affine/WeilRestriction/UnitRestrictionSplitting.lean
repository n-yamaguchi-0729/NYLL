/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionGeometry
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.Projective

/-! # Constructing split coordinates for finite-algebra unit restriction -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Module

namespace SchemeTheory.Affine.UnitNormPolynomial

variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [FiniteDimensional K A]
  {κ : Type} [Fintype κ] [DecidableEq κ]
  (bB : Basis κ K B) (f : A →ₐ[K] B) (hf : Function.Surjective f)

omit [Fintype κ] [DecidableEq κ] in
include hf in
/-- A surjective finite-algebra map admits actual basis coordinates in which it
is the projection onto the target basis. -/
theorem exists_splitBasis :
    ∃ (m : ℕ) (bA : Basis (Fin m ⊕ κ) K A),
      (∀ i, f (bA (Sum.inl i)) = 0) ∧ (∀ j, f (bA (Sum.inr j)) = bB j) := by
  let p : A →ₗ[K] B := f.toLinearMap
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hps (b : B) : p (s b) = b := LinearMap.congr_fun hs b
  let L : LinearMap.ker p × B →ₗ[K] A := (LinearMap.ker p).subtype.coprod s
  have hL (z : LinearMap.ker p × B) : p (L z) = z.2 := by
    change p ((z.1 : A) + s z.2) = z.2
    rw [map_add, z.1.property, hps, zero_add]
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
    have hk : a - s (p a) ∈ LinearMap.ker p := by
      change p (a - s (p a)) = 0
      rw [map_sub, hps, sub_self]
    refine ⟨(⟨a - s (p a), hk⟩, p a), ?_⟩
    change a - s (p a) + s (p a) = a
    exact sub_add_cancel _ _
  let e : (LinearMap.ker p × B) ≃ₗ[K] A := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  let bk : Basis (Fin (Module.finrank K (LinearMap.ker p))) K (LinearMap.ker p) :=
    Module.finBasis K (LinearMap.ker p)
  refine ⟨Module.finrank K (LinearMap.ker p), (bk.prod bB).map e, ?_, ?_⟩
  · intro i
    rw [Basis.map_apply]
    change p (L ((bk.prod bB) (Sum.inl i))) = 0
    rw [hL, Basis.prod_apply_inl_snd]
  · intro j
    rw [Basis.map_apply]
    change p (L ((bk.prod bB) (Sum.inr j))) = bB j
    rw [hL, Basis.prod_apply_inr_snd]

include hf in
/-- The split coordinates used for smoothness are supplied by the actual algebra
surjection, without an additional splitting hypothesis. -/
theorem exists_smooth_restrictionMap :
    ∃ (m : ℕ) (bA : Basis (Fin m ⊕ κ) K A), Smooth (restrictionMap bA bB f) := by
  obtain ⟨m, bA, hleft, hright⟩ := exists_splitBasis bB f hf
  exact ⟨m, bA, smooth_restrictionMap_of_splitBasis bA bB f hleft hright⟩

include hf in
/-- Every finite-dimensional algebra surjection induces a smooth morphism of its
actual unit norm opens, for the originally supplied bases. -/
theorem smooth_restrictionMap {ι : Type} [Fintype ι] [DecidableEq ι]
    (bA : Basis ι K A) : Smooth (restrictionMap bA bB f) := by
  obtain ⟨m, bA', hleft, hright⟩ := exists_splitBasis bB f hf
  have : IsIso (restrictionMap bA bA' (AlgHom.id K A)) :=
    isIso_restrictionMap_id bA bA'
  have : Smooth (restrictionMap bA' bB f) :=
    smooth_restrictionMap_of_splitBasis bA' bB f hleft hright
  have hcomp : Smooth (restrictionMap bA bA' (AlgHom.id K A) ≫
      restrictionMap bA' bB f) := inferInstance
  simpa only [restrictionMap_comp, AlgHom.comp_id] using hcomp

end SchemeTheory.Affine.UnitNormPolynomial
