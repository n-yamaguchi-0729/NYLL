/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestrictionSheaf
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientGroupScheme

/-! # The actual norm model represents the unit restriction square -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite Module
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientSchemePresheaf WeilRestrictionUnits

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bA : Basis ι R A) (bB : Basis κ R B)

/-- The concrete norm open as a scheme over its original coefficient spectrum. -/
def normRepresentingObject : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (CoordinateRing bA)))

/-- The norm open represents tensor units on arbitrary scheme tests, using the
actual relative Gamma--Spec adjunction. -/
def normSchemeRepresentable : (schemeTensorUnitsPresheaf R A).RepresentableBy
    (normRepresentingObject bA) where
  homEquiv {T} :=
    (affinePointEquiv (CommAlgCat.of R (CoordinateRing bA)) T).symm.trans (homEquivUnits bA)
  homEquiv_comp {_ T'} f g :=
    (congrArg (homEquivUnits bA)
      (affinePointEquiv_symm_comp (CommAlgCat.of R (CoordinateRing bA)) f g)).trans
        (homEquivUnits_comp bA
          ((affinePointEquiv (CommAlgCat.of R (CoordinateRing bA)) T').symm g) (sectionsMap f))

/-- The actual norm restriction morphism, retaining its coefficient structure. -/
def restrictionOver (f : A →ₐ[R] B) : normRepresentingObject bA ⟶ normRepresentingObject bB :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (restrictionRingHom bA bB f)).op

/-- Its underlying scheme morphism is the proved smooth, surjective norm restriction. -/
theorem restrictionOver_left (f : A →ₐ[R] B) :
    (restrictionOver bA bB f).left = restrictionMap bA bB f := rfl

/-- The norm representation carries restriction to actual tensor-unit restriction. -/
theorem normSchemeRepresentable_restriction (f : A →ₐ[R] B)
    {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ normRepresentingObject bA) :
    (normSchemeRepresentable bB).homEquiv (g ≫ restrictionOver bA bB f) =
      ScalarQuotientPresheaf.algebraUnitRestriction f
        ((normSchemeRepresentable bA).homEquiv g) := by
  have h := affinePointEquiv_symm_postcomp
    (B := CommAlgCat.of R (CoordinateRing bB))
    (B' := CommAlgCat.of R (CoordinateRing bA)) g (restrictionRingHom bA bB f)
  exact (congrArg (homEquivUnits bB) h).trans (restrictionRingHom_homEquiv bA bB f _)

/-- The represented unit presheaf in the value universe of the big site. -/
def liftedNormSchemeRepresentable :
    (schemeTensorUnitsPresheaf R A ⋙ uliftFunctor.{u + 1, u}).RepresentableBy
      (normRepresentingObject bA) :=
  Functor.representableByUliftFunctorEquiv.symm (normSchemeRepresentable bA)

omit [Fintype ι] [DecidableEq ι] in
include bA in
/-- The concrete unit classification is already a sheaf for the actual fppf topology. -/
theorem liftedNormScheme_isSheaf [Finite ι] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (schemeTensorUnitsPresheaf R A ⋙ uliftFunctor.{u + 1, u}) := by
  classical
  let := Fintype.ofFinite ι
  have := (liftedNormSchemeRepresentable bA).isRepresentable
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The actual represented unit presheaf is identified with its fppf sheafification. -/
def normSheafRepresentingIso :
    uliftYoneda.{u + 1}.obj (normRepresentingObject bA) ≅
      sheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (schemeTensorUnitsPresheaf R A ⋙ uliftFunctor.{u + 1, u}) :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _ (liftedNormSchemeRepresentable bA)) ≪≫
    isoSheafify _ (liftedNormScheme_isSheaf bA)

end SchemeTheory.Affine.UnitNormPolynomial

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientSchemePresheaf WeilRestrictionUnits

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The inclusion of degree-zero norm fractions retains the original coefficient action. -/
def quotientRingHom : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] CoordinateRing b where
  __ := algebraMap (ProjectiveUnitOpen.CoordinateRing b) (CoordinateRing b)
  commutes' _ := rfl

/-- The actual projective-class map as a morphism over the coefficient scheme. -/
def quotientOver : normRepresentingObject b ⟶ ScalarQuotientSchemePresheaf.representingObject b :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (quotientRingHom b)).op

/-- The represented map is literally the projective-class map of the norm open. -/
theorem quotientOver_left : (quotientOver b).left = ProjectiveUnitOpen.quotientMap b := rfl

/-- Passing to the actual projective point sends the classified norm unit to the
composite with the original projective-class morphism. -/
theorem normSchemeRepresentable_quotient
    {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ normRepresentingObject b) :
    (comparisonSmall b).app (op T)
        (QuotientGroup.mk ((normSchemeRepresentable b).homEquiv g)) = g ≫ quotientOver b := by
  let a := (affinePointEquiv (CommAlgCat.of R (CoordinateRing b)) T).symm g
  have hp : ScalarQuotientPresheaf.projectivePointAlgHom b (homEquivUnits b a) =
      a.comp (quotientRingHom b) := by
    apply AlgHom.ext
    intro z
    change unitToHom b (homToUnit b a)
      (algebraMap (ProjectiveUnitOpen.CoordinateRing b) (CoordinateRing b) z) =
      a (algebraMap (ProjectiveUnitOpen.CoordinateRing b) (CoordinateRing b) z)
    rw [unitToHom_homToUnit]
  change affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b)) T
    (ScalarQuotientPresheaf.projectivePointAlgHom b (homEquivUnits b a)) = _
  rw [hp, affinePointEquiv_postcomp]
  exact congrArg (fun h : T ⟶ normRepresentingObject b => h ≫ quotientOver b)
    ((affinePointEquiv (CommAlgCat.of R (CoordinateRing b)) T).apply_symm_apply g)

end SchemeTheory.Affine.UnitNormPolynomial
