/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusScalarExtensionNaturality
import Nyll.JacobianVarieties.Generalized.PicardGroupSheaf
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupSheaf
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Over

/-!
# Scalar extension of the actual modulus Picard group sheaves

Restriction along the map of slice sites is continuous and cocontinuous.
The proved group-presheaf comparison therefore commutes with actual fppf
sheafification, retaining the canonical map from chosen-rigidified classes.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- Scalar extension of the full modulus tensor group sheaf. -/
def modulusPicardGroupSheafScalarExtensionIso :
    modulusPicardGroupSheaf (baseChange R c R') (modulusBaseChange c i (specMap R R')) ≅
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap R R')).obj
        (modulusPicardGroupSheaf c i) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
    CommGrpCat.{u + 1}).mapIso (modulusPicardGroupScalarExtensionIso c i R') ≪≫
      ((Over.map (specMap R R')).pushforwardContinuousSheafificationCompatibility
        CommGrpCat.{u + 1} (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).app (modulusPicardGroupPresheaf c i)

/-- Scalar extension of Picard-zero uses the same actual modulus and the same geometric cut. -/
def modulusPicardZeroGroupSheafScalarExtensionIso :
    modulusPicardZeroGroupSheaf (baseChange R c R') (modulusBaseChange c i (specMap R R')) ≅
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap R R')).obj
        (modulusPicardZeroGroupSheaf c i) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
    CommGrpCat.{u + 1}).mapIso (modulusPicardZeroGroupScalarExtensionIso c i R') ≪≫
      ((Over.map (specMap R R')).pushforwardContinuousSheafificationCompatibility
        CommGrpCat.{u + 1} (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).app
          (modulusPicardZeroGroupPresheaf c i)

/-- The sheaf comparison is the actual scalar-extension map on represented bundle classes. -/
@[reassoc] theorem toSheafify_modulusPicardZeroGroupScalarExtension :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
        (modulusPicardZeroGroupPresheaf (baseChange R c R')
          (modulusBaseChange c i (specMap R R'))) ≫
      (modulusPicardZeroGroupSheafScalarExtensionIso c i R').hom.hom =
        (modulusPicardZeroGroupScalarExtensionIso c i R').hom ≫
          Functor.whiskerLeft (Over.map (specMap R R')).op
            (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
              (modulusPicardZeroGroupPresheaf c i)) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let J' := Scheme.fppfTopology.over (Spec (CommRingCat.of R'))
  let F := modulusPicardZeroGroupPresheaf c i
  let F' := modulusPicardZeroGroupPresheaf (baseChange R c R')
    (modulusBaseChange c i (specMap R R'))
  let a := modulusPicardZeroGroupScalarExtensionIso c i R'
  change toSheafify J' F' ≫ (sheafifyMap J' a.hom ≫
      (((Over.map (specMap R R')).pushforwardContinuousSheafificationCompatibility
        CommGrpCat.{u + 1} J' J).hom.app F).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    Functor.toSheafify_pullbackSheafificationCompatibility]
  rfl

end AlgebraicGeometry.GeneralizedJacobian
