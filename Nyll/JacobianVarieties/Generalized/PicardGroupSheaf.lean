/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardGroupFunctor
import Nyll.JacobianVarieties.Generalized.PicardSheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# The commutative group sheaf of modulus-rigidified classes

Sheafification in commutative groups is supplied by actual filtered colimits
and limits of commutative groups. Forgetting the group structure commutes with
this sheafification. Thus the underlying sheaf is canonically the previously
constructed fppf sheaf of chosen-rigidified line-bundle classes, with compatible
units from actual bundles.
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

private instance filteredCommGrpHasColimitsOfShape
    {K : Type v} [SmallCategory K] [IsFiltered K] :
    HasColimitsOfShape K CommGrpCat.{v} where
  has_colimit F := HasColimit.mk
    { cocone := CommGrpCat.FilteredColimits.colimitCocone F
      isColimit := CommGrpCat.FilteredColimits.colimitCoconeIsColimit F }

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- The fppf sheaf of commutative groups obtained from tensor product of
chosen-rigidified line-bundle classes. -/
def modulusPicardGroupSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).obj (modulusPicardGroupPresheaf c i)

/-- Actual compatible-isomorphism classes map to the group sheaf by a natural
family of group homomorphisms. -/
def toModulusPicardGroupSheaf :
    modulusPicardGroupPresheaf c i ⟶ (modulusPicardGroupSheaf c i).obj :=
  CategoryTheory.toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (modulusPicardGroupPresheaf c i)

/-- The group sheaf has the same underlying presheaf as the canonical fppf
sheafification of the original chosen-rigidification presheaf. -/
def modulusPicardGroupSheafForgetIso :
    (modulusPicardGroupSheaf c i).obj ⋙ forget CommGrpCat ≅
      (modulusPicardSheaf c i).obj :=
  (CategoryTheory.sheafifyComposeIso
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (forget CommGrpCat.{u + 1}) (modulusPicardGroupPresheaf c i)).symm

/-- The comparison identifies the two canonical maps from actual bundle classes. -/
@[reassoc] theorem toModulusPicardGroupSheaf_forgetIso :
    Functor.whiskerRight (toModulusPicardGroupSheaf c i) (forget CommGrpCat) ≫
      (modulusPicardGroupSheafForgetIso c i).hom = toModulusPicardSheaf c i :=
  CategoryTheory.sheafComposeIso_inv_fac
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (forget CommGrpCat.{u + 1}) (modulusPicardGroupPresheaf c i)

variable {c i}

/-- A natural group homomorphism from actual classes into an fppf group sheaf
extends through group sheafification. -/
def modulusPicardGroupSheafLift
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1}}
    (a : modulusPicardGroupPresheaf c i ⟶ Q.obj) : modulusPicardGroupSheaf c i ⟶ Q :=
  ((sheafificationAdjunction (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).homEquiv (modulusPicardGroupPresheaf c i) Q).symm a

@[reassoc] theorem toModulusPicardGroupSheaf_lift
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1}}
    (a : modulusPicardGroupPresheaf c i ⟶ Q.obj) :
    toModulusPicardGroupSheaf c i ≫ (modulusPicardGroupSheafLift a).hom = a :=
  CategoryTheory.toSheafify_sheafifyLift
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) a Q.property

theorem modulusPicardGroupSheafLift_unique
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1}}
    (a : modulusPicardGroupPresheaf c i ⟶ Q.obj) (g : modulusPicardGroupSheaf c i ⟶ Q)
    (h : toModulusPicardGroupSheaf c i ≫ g.hom = a) : g = modulusPicardGroupSheafLift a := by
  apply Sheaf.hom_ext
  exact CategoryTheory.sheafifyLift_unique
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) a Q.property g.hom h

end AlgebraicGeometry.GeneralizedJacobian
