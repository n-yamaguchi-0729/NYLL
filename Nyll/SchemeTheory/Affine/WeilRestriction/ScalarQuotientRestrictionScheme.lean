/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitNormSchemeRepresentation

/-! # The actual Cartesian restriction square of unit and scalar quotient schemes -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientSchemePresheaf WeilRestrictionUnits

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bA : Basis ι R A) (bB : Basis κ R B)

/-- The actual classification by units, expressed as the represented presheaf isomorphism. -/
def normPresheafRepresentingIso :
    uliftYoneda.{u + 1}.obj (normRepresentingObject bA) ≅
      schemeTensorUnitsPresheaf R A ⋙ uliftFunctor.{u + 1, u} :=
  Functor.RepresentableBy.equivUliftYonedaIso _ _ (liftedNormSchemeRepresentable bA)

/-- Restriction agrees with the actual norm classification before sheafification. -/
@[reassoc] theorem normPresheafRepresentingIso_restriction (f : A →ₐ[R] B) :
    (normPresheafRepresentingIso bA).hom ≫
      Functor.whiskerRight (tensorUnitRestrictionPresheaf f) uliftFunctor.{u + 1, u} =
    uliftYoneda.map (restrictionOver bA bB f) ≫ (normPresheafRepresentingIso bB).hom := by
  apply NatTrans.ext
  funext T
  apply TypeCat.homEquiv.injective
  funext g
  apply ULift.ext
  change ScalarQuotientPresheaf.algebraUnitRestriction f
    ((normSchemeRepresentable bA).homEquiv g.down) =
      (normSchemeRepresentable bB).homEquiv (g.down ≫ restrictionOver bA bB f)
  exact (normSchemeRepresentable_restriction bA bB f g.down).symm

/-- The canonical sheafification preserves the actual norm restriction classification. -/
@[reassoc] theorem normSheafRepresentingIso_restriction (f : A →ₐ[R] B) :
    (normSheafRepresentingIso bA).hom ≫
      sheafifyMap (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Functor.whiskerRight (tensorUnitRestrictionPresheaf f) uliftFunctor.{u + 1, u}) =
    uliftYoneda.map (restrictionOver bA bB f) ≫ (normSheafRepresentingIso bB).hom := by
  change ((normPresheafRepresentingIso bA).hom ≫ toSheafify _ _) ≫ _ =
    _ ≫ ((normPresheafRepresentingIso bB).hom ≫ toSheafify _ _)
  rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc,
    normPresheafRepresentingIso_restriction bA bB f, Category.assoc]

end SchemeTheory.Affine.UnitNormPolynomial

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

open UnitNormPolynomial

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {n m : ℕ} (bA : Basis (Fin (n + 1)) R A) (bB : Basis (Fin (m + 1)) R B)
  (f : A →ₐ[R] B)

/-- The canonical restriction map of the actual projective norm models, obtained from
the proved fppf representation of literal scalar quotient restriction. -/
def quotientRestrictionOver : representingObject bA ⟶ representingObject bB :=
  uliftYoneda.{u + 1}.preimage
    ((sheafifiedComparisonIso bA).inv ≫
      sheafifyMap (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Functor.whiskerRight
          (Functor.whiskerRight (algebraRestrictionPresheaf f) (forget CommGrpCat.{u}))
          uliftFunctor.{u + 1, u}) ≫
      (sheafifiedComparisonIso bB).hom)

/-- The represented restriction is exactly the sheafified algebra restriction. -/
theorem uliftYoneda_map_quotientRestrictionOver :
    uliftYoneda.{u + 1}.map (quotientRestrictionOver bA bB f) =
    (sheafifiedComparisonIso bA).inv ≫
      sheafifyMap (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Functor.whiskerRight
          (Functor.whiskerRight (algebraRestrictionPresheaf f) (forget CommGrpCat.{u}))
          uliftFunctor.{u + 1, u}) ≫
      (sheafifiedComparisonIso bB).hom :=
  uliftYoneda.map_preimage _

/-- The actual morphism of projective norm opens underlying quotient restriction. -/
def quotientRestrictionMap : ProjectiveUnitOpen.carrier bA ⟶ ProjectiveUnitOpen.carrier bB :=
  (quotientRestrictionOver bA bB f).left

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientSchemePresheaf WeilRestrictionUnits

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The presheaf representation identifies the quotient of an actual unit with its
original projective-class morphism. -/
@[reassoc] theorem normPresheafRepresentingIso_quotient :
    (normPresheafRepresentingIso b).hom ≫
      Functor.whiskerRight (tensorUnitsToScalarQuotient R A) uliftFunctor.{u + 1, u} ≫
      comparison b = uliftYoneda.map (quotientOver b) := by
  apply NatTrans.ext
  funext T
  apply TypeCat.homEquiv.injective
  funext g
  apply ULift.ext
  exact normSchemeRepresentable_quotient b g.down

/-- The fppf representation identifies the actual quotient morphism, with its
canonical sheafification map rather than an arbitrary isomorphism of carriers. -/
@[reassoc] theorem normSheafRepresentingIso_quotient :
    (normSheafRepresentingIso b).hom ≫
      sheafifyMap (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Functor.whiskerRight (tensorUnitsToScalarQuotient R A) uliftFunctor.{u + 1, u}) =
    uliftYoneda.map (quotientOver b) ≫ (sheafifiedComparisonIso b).inv := by
  let q : (schemeTensorUnitsPresheaf R A ⋙ uliftFunctor.{u + 1, u}) ⟶
      (liftedGroupPresheaf R A ⋙ forget CommGrpCat.{u + 1}) :=
    Functor.whiskerRight (tensorUnitsToScalarQuotient R A) uliftFunctor.{u + 1, u}
  change (normSheafRepresentingIso b).hom ≫ sheafifyMap _ q = _
  symm
  apply (sheafifiedComparisonIso b).comp_inv_eq.mpr
  symm
  change (((normPresheafRepresentingIso b).hom ≫ toSheafify _ _) ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rw [← toSheafify_naturality_assoc, toSheafify_sheafifiedComparisonIso]
  exact normPresheafRepresentingIso_quotient b

end SchemeTheory.Affine.UnitNormPolynomial

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

open UnitNormPolynomial

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {n m : ℕ} (bA : Basis (Fin (n + 1)) R A) (bB : Basis (Fin (m + 1)) R B)
  (f : A →ₐ[R] B)

/-- The restriction square of the actual unit and projective norm models is Cartesian.
Every comparison is supplied by the constructed representation and scalar orbit proofs. -/
theorem quotientRestrictionOver_isPullback :
    IsPullback (quotientOver bA) (restrictionOver bA bB f)
      (quotientRestrictionOver bA bB f) (quotientOver bB) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  have hs := (sheafified_restriction_isPullback f bB).map
    (sheafToPresheaf J (Type (u + 1)))
  have hy : IsPullback (uliftYoneda.{u + 1}.map (quotientOver bA))
      (uliftYoneda.map (restrictionOver bA bB f))
      (uliftYoneda.map (quotientRestrictionOver bA bB f))
      (uliftYoneda.map (quotientOver bB)) := by
    apply hs.of_iso' (normSheafRepresentingIso bA) (sheafifiedComparisonIso bA).symm
      (normSheafRepresentingIso bB) (sheafifiedComparisonIso bB).symm
    · exact normSheafRepresentingIso_quotient bA
    · exact normSheafRepresentingIso_restriction bA bB f
    · change (sheafifiedComparisonIso bA).inv ≫ _ =
        uliftYoneda.map (quotientRestrictionOver bA bB f) ≫ (sheafifiedComparisonIso bB).inv
      symm
      apply (sheafifiedComparisonIso bB).comp_inv_eq.mpr
      exact (uliftYoneda_map_quotientRestrictionOver bA bB f).trans
        (Category.assoc _ _ _).symm
    · exact normSheafRepresentingIso_quotient bB
  exact hy.of_map_of_faithful uliftYoneda

/-- The underlying actual scheme square, used to transfer geometry from unit restriction. -/
theorem quotientRestrictionMap_isPullback :
    IsPullback (ProjectiveUnitOpen.quotientMap bA) (restrictionMap bA bB f)
      (quotientRestrictionMap bA bB f) (ProjectiveUnitOpen.quotientMap bB) := by
  exact (quotientRestrictionOver_isPullback bA bB f).map
    (Over.forget (Spec (CommRingCat.of R)))

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
