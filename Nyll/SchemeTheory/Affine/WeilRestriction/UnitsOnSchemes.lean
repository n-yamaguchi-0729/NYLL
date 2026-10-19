/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.Units
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientSchemePresheaf

/-!
# Actual units on scheme-valued tests

The relative Gamma--Spec adjunction identifies maps to the multiplicative
group with actual global units. Applied to the finite-free Weil restriction,
this compares tensor-algebra units on global sections with units on the
actual scheme fibre product, naturally on arbitrary test schemes.

This file proves the natural equivalence of the underlying presheaves.
Compatibility with scalar multiplication and the quotient is separate.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open SchemeTheory.Affine.ScalarQuotientSchemePresheaf

namespace SchemeTheory.Affine.WeilRestrictionUnits

variable (R : Type u) [CommRing R]

/-- Actual global units on all schemes over the coefficient spectrum. -/
def schemeUnitsPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type u :=
  (AlgebraicGeometry.algΓ (CommRingCat.of R)).op ⋙
    (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ unitsFunctor R

/-- The usual multiplicative-group carrier represents actual global units. -/
def schemeUnitsRepresentable : (schemeUnitsPresheaf R).RepresentableBy
    (specBOver (R := R) (B := CoordinateRing R)) where
  homEquiv {T} :=
    (affinePointEquiv (CommAlgCat.of R (CoordinateRing R)) T).symm.trans homEquivUnits
  homEquiv_comp {T T'} f g :=
    (congrArg (homEquivUnits (R := R) (S := sectionsAlgebra R T))
      (affinePointEquiv_symm_comp (CommAlgCat.of R (CoordinateRing R)) f g)).trans
        (homEquivUnits_comp
          ((affinePointEquiv (CommAlgCat.of R (CoordinateRing R)) T').symm g)
          (sectionsMap f))

variable (A : Type u) [CommRing A] [Algebra R A]

/-- Units in the actual product of a test scheme with the coefficient algebra's spectrum. -/
def productUnitsPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type u :=
  (MonoidalCategory.tensorRight (specAOver (R := R) (A := A))).op ⋙ schemeUnitsPresheaf R

/-- Actual maps from the product to the multiplicative group classify its units. -/
def internalHomUnitsIso :
    (MonoidalCategory.tensorRight (specAOver (R := R) (A := A))).op ⋙
      yoneda.obj (specBOver (R := R) (B := CoordinateRing R)) ≅
        productUnitsPresheaf R A :=
  Functor.isoWhiskerLeft _ (schemeUnitsRepresentable R).toIso

/-- Tensor-algebra units evaluated on global sections of arbitrary test schemes. -/
def schemeTensorUnitsPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type u :=
  (AlgebraicGeometry.algΓ (CommRingCat.of R)).op ⋙
    (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ tensorUnitsFunctor R A

variable [Module.Free R A] [Module.Finite R A]

/-- The same affine Weil-restriction carrier represents actual product units. -/
def productUnitsRepresentable :
    (productUnitsPresheaf R A).RepresentableBy (unitsScheme R A) :=
  (unitsSchemeRepresentable R A).ofIso (internalHomUnitsIso R A)

/-- The tensor-unit algebraic representation extends to arbitrary scheme tests. -/
def tensorUnitsAlgHomEquiv (C : CommAlgCat.{u} R) :
    (unitsRepresentingAlgebra R A →ₐ[R] C) ≃ (tensorUnitsFunctor R A).obj C where
  toFun f := (tensorUnitsCorepresentable R A).homEquiv (CommAlgCat.ofHom f)
  invFun a := ((tensorUnitsCorepresentable R A).homEquiv.symm a).hom
  left_inv f := congrArg (fun g : unitsRepresentingAlgebra R A ⟶ C => g.hom)
    ((tensorUnitsCorepresentable R A).homEquiv.symm_apply_apply (CommAlgCat.ofHom f))
  right_inv a := (tensorUnitsCorepresentable R A).homEquiv.apply_symm_apply a

theorem tensorUnitsAlgHomEquiv_comp {C D : CommAlgCat.{u} R}
    (f : unitsRepresentingAlgebra R A →ₐ[R] C) (g : C →ₐ[R] D) :
    tensorUnitsAlgHomEquiv R A D (g.comp f) =
      (tensorUnitsFunctor R A).map (CommAlgCat.ofHom g) (tensorUnitsAlgHomEquiv R A C f) :=
  (tensorUnitsCorepresentable R A).homEquiv_comp (CommAlgCat.ofHom g) (CommAlgCat.ofHom f)

/-- The actual affine carrier represents tensor units on every scheme test. -/
def schemeTensorUnitsRepresentable :
    (schemeTensorUnitsPresheaf R A).RepresentableBy (unitsScheme R A) where
  homEquiv {T} := (affinePointEquiv (unitsRepresentingAlgebra R A) T).symm.trans
    (tensorUnitsAlgHomEquiv R A (sectionsAlgebra R T))
  homEquiv_comp {T T'} f g :=
    (congrArg (tensorUnitsAlgHomEquiv R A (sectionsAlgebra R T))
      (affinePointEquiv_symm_comp (unitsRepresentingAlgebra R A) f g)).trans
        (tensorUnitsAlgHomEquiv_comp R A
          ((affinePointEquiv (unitsRepresentingAlgebra R A) T').symm g) (sectionsMap f))

/-- The two actual presheaves have the same affine representer, including naturality. -/
def tensorUnitsProductUnitsIso : schemeTensorUnitsPresheaf R A ≅ productUnitsPresheaf R A :=
  (schemeTensorUnitsRepresentable R A).toIso.symm ≪≫ (productUnitsRepresentable R A).toIso

end SchemeTheory.Affine.WeilRestrictionUnits
