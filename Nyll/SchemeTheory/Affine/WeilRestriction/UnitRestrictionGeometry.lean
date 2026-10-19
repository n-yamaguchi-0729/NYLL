/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestriction
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth

/-! # Smoothness of unit restriction in split coordinates -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct BigOperators

namespace SchemeTheory.Affine.UnitNormPolynomial

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bA : Basis (ι ⊕ κ) R A) (bB : Basis κ R B) (f : A →ₐ[R] B)
  (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)

omit [DecidableEq ι] [DecidableEq κ] in
include hleft hright in
/-- In coordinates adapted to a surjection, tensor restriction is the coordinate projection. -/
theorem restriction_element {S : Type u} [CommRing S] [Algebra R S]
    (x : ι ⊕ κ → S) :
    Algebra.TensorProduct.map (AlgHom.id R S) f (element bA x) =
      element bB (fun j => x (Sum.inr j)) := by
  simp only [element, map_add, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Fintype.sum_sum_type, hleft, hright, TensorProduct.tmul_zero, Finset.sum_const_zero,
    zero_add]

include hleft hright in
/-- The norm-open restriction extends the ordinary affine-space projection. -/
theorem restrictionRingHom_comp_localization :
    (restrictionRingHom bA bB f).comp
        (IsScalarTower.toAlgHom R (MvPolynomial κ R) (CoordinateRing bB)) =
      (IsScalarTower.toAlgHom R (MvPolynomial (ι ⊕ κ) R) (CoordinateRing bA)).comp
        (MvPolynomial.rename Sum.inr) := by
  apply MvPolynomial.algHom_ext
  intro j
  change restrictionRingHom bA bB f
      (algebraMap (MvPolynomial κ R) (CoordinateRing bB) (MvPolynomial.X j)) =
    algebraMap (MvPolynomial (ι ⊕ κ) R) (CoordinateRing bA)
      (MvPolynomial.rename Sum.inr (MvPolynomial.X j))
  rw [restrictionRingHom_coordinates, restriction_element bA bB f hleft hright,
    coordinates_element, MvPolynomial.rename_X]

include hleft hright in
/-- The actual square of affine unit opens commutes with coordinate projection. -/
theorem restrictionMap_square :
    restrictionMap bA bB f ≫ unitOpenι bB =
      unitOpenι bA ≫ Spec.map (CommRingCat.ofHom
        (MvPolynomial.rename Sum.inr : MvPolynomial κ R →ₐ[R]
          MvPolynomial (ι ⊕ κ) R).toRingHom) := by
  rw [restrictionMap, unitOpenι, unitOpenι, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom
    (restrictionRingHom_comp_localization bA bB f hleft hright)

omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ] in
/-- The linear projection in split coordinates is smooth. -/
theorem smooth_specMap_rename_inr [Finite ι] :
    Smooth (Spec.map (CommRingCat.ofHom
      (MvPolynomial.rename Sum.inr : MvPolynomial κ R →ₐ[R]
        MvPolynomial (ι ⊕ κ) R).toRingHom)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  have hs : (algebraMap (MvPolynomial κ R) (MvPolynomial ι (MvPolynomial κ R))).Smooth :=
    RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  have he : (MvPolynomial.rename Sum.inr : MvPolynomial κ R →ₐ[R]
      MvPolynomial (ι ⊕ κ) R).toRingHom =
    (MvPolynomial.sumAlgEquiv R ι κ).symm.toRingHom.comp
      (algebraMap (MvPolynomial κ R) (MvPolynomial ι (MvPolynomial κ R))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.rename Sum.inr (MvPolynomial.C r) =
        (MvPolynomial.sumAlgEquiv R ι κ).symm (MvPolynomial.C (MvPolynomial.C r))
      rw [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_symm_C_C]
    · intro j
      change MvPolynomial.rename Sum.inr (MvPolynomial.X j) =
        (MvPolynomial.sumAlgEquiv R ι κ).symm (MvPolynomial.C (MvPolynomial.X j))
      rw [MvPolynomial.rename_X, MvPolynomial.sumAlgEquiv_symm_C_X]
  rw [he]
  exact hs.comp (RingHom.Smooth.of_bijective (MvPolynomial.sumAlgEquiv R ι κ).symm.bijective)

include hleft hright in
/-- Restriction between the actual unit norm opens is smooth in adapted coordinates. -/
theorem smooth_restrictionMap_of_splitBasis : Smooth (restrictionMap bA bB f) := by
  have : Smooth (Spec.map (CommRingCat.ofHom
      (MvPolynomial.rename Sum.inr : MvPolynomial κ R →ₐ[R]
        MvPolynomial (ι ⊕ κ) R).toRingHom)) := smooth_specMap_rename_inr (R := R)
  have hcomp : Smooth (restrictionMap bA bB f ≫ unitOpenι bB) := by
    rw [restrictionMap_square bA bB f hleft hright]
    infer_instance
  have : MorphismProperty.HasOfPostcompProperty
      (@Smooth : MorphismProperty Scheme.{u})
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
      (P := (@Smooth : MorphismProperty Scheme.{u}))
  exact MorphismProperty.of_postcomp (@Smooth : MorphismProperty Scheme.{u})
    (W' := MorphismProperty.monomorphisms Scheme.{u})
    (restrictionMap bA bB f) (unitOpenι bB) (inferInstance : Mono (unitOpenι bB)) hcomp

end SchemeTheory.Affine.UnitNormPolynomial
