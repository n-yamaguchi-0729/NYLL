/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionSplitting
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionSurjective
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Geometric fibres of actual finite-algebra unit restriction -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

namespace SchemeTheory.Affine.UnitNormPolynomial

local instance : MorphismProperty.RespectsIso
    (@GeometricallyIrreducible : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := (@GeometricallyIrreducible : MorphismProperty Scheme.{u}))

/-- Polynomial affine space with a small index type is geometrically irreducible
over its coefficient ring. -/
theorem geometricallyIrreducible_specMap_C (R : Type u) [CommRing R] (ν : Type) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial ν R)))) := by
  let e := (MvPolynomial.renameEquiv R (Equiv.ulift : ULift.{u} ν ≃ ν)).toRingEquiv
    |>.toCommRingCatIso
  have hlarge : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial (ULift.{u} ν) R)))) := by
    change GeometricallyIrreducible (Spec.map (CommRingCat.ofHom MvPolynomial.C))
    rw [← AffineSpace.SpecIso_inv_over (n := ULift.{u} ν) (CommRingCat.of R),
      MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyIrreducible : MorphismProperty Scheme.{u}))]
    infer_instance
  have hcomp : GeometricallyIrreducible (Spec.map e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (ULift.{u} ν) R)))) := by
    rw [MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyIrreducible : MorphismProperty Scheme.{u}))]
    exact hlarge
  have he : Spec.map e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (ULift.{u} ν) R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ν R))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (MvPolynomial.renameEquiv R (Equiv.ulift : ULift.{u} ν ≃ ν)).toAlgHom.comp_algebraMap
  rwa [he] at hcomp

/-- The coordinate projection is geometrically irreducible, including relative
dimension zero. -/
theorem geometricallyIrreducible_specMap_rename_inr
    (R : Type u) [CommRing R] (ι κ : Type) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (MvPolynomial.rename Sum.inr : MvPolynomial κ R →ₐ[R]
        MvPolynomial (ι ⊕ κ) R).toRingHom)) := by
  let e := (MvPolynomial.sumAlgEquiv R ι κ).symm.toRingEquiv.toCommRingCatIso
  have hcomp : GeometricallyIrreducible (Spec.map e.hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial κ R) (MvPolynomial ι (MvPolynomial κ R))))) := by
    rw [MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyIrreducible : MorphismProperty Scheme.{u}))]
    exact geometricallyIrreducible_specMap_C (MvPolynomial κ R) ι
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
  have hmap : Spec.map (CommRingCat.ofHom
      ((MvPolynomial.sumAlgEquiv R ι κ).symm.toRingHom.comp
        (algebraMap (MvPolynomial κ R) (MvPolynomial ι (MvPolynomial κ R))))) =
      Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial κ R) (MvPolynomial ι (MvPolynomial κ R)))) :=
    Spec.map_comp (CommRingCat.ofHom
      (algebraMap (MvPolynomial κ R) (MvPolynomial ι (MvPolynomial κ R)))) e.hom
  rw [hmap]
  exact hcomp

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bA : Basis (ι ⊕ κ) R A) (bB : Basis κ R B) (f : A →ₐ[R] B)
  (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)
  (hf : Function.Surjective f)

include hleft hright hf in
/-- Each geometric fibre of restriction is a nonempty open subset of the affine
space supplied by the split coordinates. -/
theorem geometricallyIrreducible_restrictionMap_of_splitBasis :
    GeometricallyIrreducible (restrictionMap bA bB f) := by
  let π := Spec.map (CommRingCat.ofHom
    (MvPolynomial.rename Sum.inr : MvPolynomial κ R →ₐ[R]
      MvPolynomial (ι ⊕ κ) R).toRingHom)
  let h : unitOpen bA ⟶ pullback π (unitOpenι bB) :=
    pullback.lift (unitOpenι bA) (restrictionMap bA bB f)
      (restrictionMap_square bA bB f hleft hright).symm
  have : IsOpenImmersion (h ≫ pullback.fst π (unitOpenι bB)) := by
    change IsOpenImmersion (pullback.lift _ _ _ ≫ pullback.fst _ _)
    rw [pullback.lift_fst]
    infer_instance
  have : IsOpenImmersion h := IsOpenImmersion.of_comp h (pullback.fst π (unitOpenι bB))
  have : GeometricallyIrreducible π :=
    geometricallyIrreducible_specMap_rename_inr R ι κ
  have : Surjective (h ≫ pullback.snd π (unitOpenι bB)) := by
    change Surjective (pullback.lift _ _ _ ≫ pullback.snd _ _)
    rw [pullback.lift_snd]
    exact surjective_restrictionMap bA bB f hf
  have hgeom : GeometricallyIrreducible (h ≫ pullback.snd π (unitOpenι bB)) := inferInstance
  simpa only [h, pullback.lift_snd] using hgeom

end SchemeTheory.Affine.UnitNormPolynomial

namespace SchemeTheory.Affine.UnitNormPolynomial

local instance : MorphismProperty.RespectsIso
    (@GeometricallyIrreducible : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := (@GeometricallyIrreducible : MorphismProperty Scheme.{u}))

variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [FiniteDimensional K A]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bA : Basis ι K A) (bB : Basis κ K B) (f : A →ₐ[K] B)
  (hf : Function.Surjective f)

include hf in
/-- Restriction along a finite-dimensional algebra surjection has geometrically
irreducible fibres for any original bases. -/
theorem geometricallyIrreducible_restrictionMap :
    GeometricallyIrreducible (restrictionMap bA bB f) := by
  obtain ⟨m, bA', hleft, hright⟩ := exists_splitBasis bB f hf
  have : IsIso (restrictionMap bA bA' (AlgHom.id K A)) :=
    isIso_restrictionMap_id bA bA'
  have hgeom : GeometricallyIrreducible (restrictionMap bA' bB f) :=
    geometricallyIrreducible_restrictionMap_of_splitBasis bA' bB f hleft hright hf
  have hcomp : GeometricallyIrreducible (restrictionMap bA bA' (AlgHom.id K A) ≫
      restrictionMap bA' bB f) := by
    rw [MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyIrreducible : MorphismProperty Scheme.{u}))]
    exact hgeom
  simpa only [restrictionMap_comp, AlgHom.comp_id] using hcomp

include hf in
/-- In particular, every geometric fibre of actual unit restriction is connected. -/
theorem geometricallyConnected_restrictionMap :
    GeometricallyConnected (restrictionMap bA bB f) := by
  constructor
  intro L _ y Z fst snd h
  have : IrreducibleSpace Z :=
    (geometricallyIrreducible_restrictionMap bA bB f hf).geometrically_irreducibleSpace
      y fst snd h
  infer_instance

end SchemeTheory.Affine.UnitNormPolynomial
