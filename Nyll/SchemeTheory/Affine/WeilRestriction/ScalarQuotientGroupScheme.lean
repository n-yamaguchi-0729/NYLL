/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientLocalBijection
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The scalar quotient as a smooth affine group scheme

The fppf sheafification of the literal scalar quotient is represented by
the projective norm open. The local bijection is proved from actual chart
sections and actual scalar orbits. Its compatibility with the canonical
sheafification map identifies the representation with the original
projective-class map. The commutative group structure is transported from
this represented group sheaf to the same concrete affine scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module

universe u v

private instance filteredCommGrpHasColimitsOfShape
    {K : Type v} [SmallCategory K] [IsFiltered K] :
    HasColimitsOfShape K CommGrpCat.{v} where
  has_colimit F := HasColimit.mk
    { cocone := CommGrpCat.FilteredColimits.colimitCocone F
      isColimit := CommGrpCat.FilteredColimits.colimitCoconeIsColimit F }

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual fppf sheafification of units modulo scalar units on all
schemes over the coefficient spectrum. -/
def scalarQuotientGroupSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).obj (liftedGroupPresheaf R A)

/-- The canonical map sends literal scalar classes to the fppf group sheaf. -/
def toScalarQuotientGroupSheaf :
    liftedGroupPresheaf R A ⟶ (scalarQuotientGroupSheaf R A).obj :=
  toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (liftedGroupPresheaf R A)

variable {R A} {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The represented fppf sheaf of points of the projective norm open. -/
def representingSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  (GrothendieckTopology.uliftYoneda.{u + 1}
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).obj (representingObject b)

/-- Sheafifying the proved local bijection gives an isomorphism onto the
represented projective norm open. -/
def sheafifiedComparisonIso :
    sheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (liftedGroupPresheaf R A ⋙ forget CommGrpCat.{u + 1}) ≅
        uliftYoneda.{u + 1}.obj (representingObject b) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  have : Presheaf.IsLocallyInjective J (comparison b) :=
    comparison_isLocallyInjective b
  have : Presheaf.IsLocallySurjective J (comparison b) :=
    comparison_isLocallySurjective b
  let m := (presheafToSheaf J (Type (u + 1))).map (comparison b)
  have : IsIso m := (J.W_iff (comparison b)).mp (J.W_of_isLocallyBijective (comparison b))
  exact (sheafToPresheaf J (Type (u + 1))).mapIso (asIso m) ≪≫
    (isoSheafify J (representingSheaf b).property).symm

/-- The sheafified comparison extends the actual projective-class map. -/
@[reassoc] theorem toSheafify_sheafifiedComparisonIso :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (liftedGroupPresheaf R A ⋙ forget CommGrpCat.{u + 1}) ≫
        (sheafifiedComparisonIso b).hom = comparison b := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  have hS : Presheaf.IsSheaf J (uliftYoneda.{u + 1}.obj (representingObject b)) :=
    (representingSheaf b).property
  change toSheafify J (liftedGroupPresheaf R A ⋙ forget CommGrpCat.{u + 1}) ≫
    (sheafifyMap J (comparison b) ≫ (isoSheafify J hS).inv) = comparison b
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  change comparison b ≫ ((isoSheafify J hS).hom ≫
    (isoSheafify J hS).inv) = comparison b
  rw [Iso.hom_inv_id, Category.comp_id]

/-- Forgetting the group-valued sheafification gives precisely the
represented projective norm-open presheaf. -/
def scalarQuotientRepresentingIso :
    (scalarQuotientGroupSheaf R A).obj ⋙ forget CommGrpCat.{u + 1} ≅
      uliftYoneda.{u + 1}.obj (representingObject b) :=
  (sheafifyComposeIso (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (forget CommGrpCat.{u + 1}) (liftedGroupPresheaf R A)).symm ≪≫
      sheafifiedComparisonIso b

/-- The representation carries the canonical scalar-class map to the
original comparison, rather than an unspecified automorphism of the carrier. -/
@[reassoc] theorem toScalarQuotientGroupSheaf_representingIso :
    Functor.whiskerRight (toScalarQuotientGroupSheaf R A) (forget CommGrpCat.{u + 1}) ≫
      (scalarQuotientRepresentingIso b).hom = comparison b := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  change Functor.whiskerRight (toSheafify J (liftedGroupPresheaf R A))
      (forget CommGrpCat.{u + 1}) ≫
    ((sheafifyComposeIso J (forget CommGrpCat.{u + 1})
      (liftedGroupPresheaf R A)).inv ≫ (sheafifiedComparisonIso b).hom) = comparison b
  rw [← Category.assoc]
  rw [sheafComposeIso_inv_fac]
  exact toSheafify_sheafifiedComparisonIso b

/-- The scalar quotient fppf group sheaf is represented by the concrete
projective norm open on arbitrary test schemes. -/
def scalarQuotientRepresentable :
    ((scalarQuotientGroupSheaf R A).obj ⋙ forget CommGrpCat.{u + 1}).RepresentableBy
      (representingObject b) :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _).symm
    (scalarQuotientRepresentingIso b).symm

/-- The actual smooth affine commutative group scheme of units modulo
scalars, constructed from its proved fppf representation. -/
def scalarQuotientCommGroupScheme : CommGrp (Over (Spec (CommRingCat.of R))) := by
  let : CommGrpObj (representingObject b) := CommGrpObj.ofRepresentableBy _
    (scalarQuotientGroupSheaf R A).obj (scalarQuotientRepresentable b)
  exact ⟨representingObject b⟩

theorem scalarQuotientCommGroupScheme_carrier :
    (scalarQuotientCommGroupScheme b).X.left = ProjectiveUnitOpen.carrier b := rfl

theorem scalarQuotientCommGroupScheme_toBase :
    (scalarQuotientCommGroupScheme b).X.hom = ProjectiveUnitOpen.toBase b :=
  (ProjectiveUnitOpen.toBase_eq b).symm

theorem smooth_scalarQuotientCommGroupScheme :
    Smooth (scalarQuotientCommGroupScheme b).X.hom := by
  rw [scalarQuotientCommGroupScheme_toBase]
  exact ProjectiveUnitOpen.smooth_toBase b

variable {b}

/-- The canonical scalar quotient has the sheafification universal
property for maps of commutative groups into every fppf group sheaf. -/
def scalarQuotientGroupSheafLift
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1}}
    (a : liftedGroupPresheaf R A ⟶ Q.obj) : scalarQuotientGroupSheaf R A ⟶ Q :=
  ((sheafificationAdjunction (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).homEquiv (liftedGroupPresheaf R A) Q).symm a

@[reassoc] theorem toScalarQuotientGroupSheaf_lift
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1}}
    (a : liftedGroupPresheaf R A ⟶ Q.obj) :
    toScalarQuotientGroupSheaf R A ≫ (scalarQuotientGroupSheafLift a).hom = a :=
  toSheafify_sheafifyLift (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) a Q.property

theorem scalarQuotientGroupSheafLift_unique
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1}}
    (a : liftedGroupPresheaf R A ⟶ Q.obj) (g : scalarQuotientGroupSheaf R A ⟶ Q)
    (h : toScalarQuotientGroupSheaf R A ≫ g.hom = a) :
    g = scalarQuotientGroupSheafLift a := by
  apply Sheaf.hom_ext
  exact sheafifyLift_unique (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    a Q.property g.hom h

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
