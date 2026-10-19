/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtension
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Over

/-! # Scalar extension of the intrinsic degree-one fppf sheaf -/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- Intrinsic degree one commutes with scalar extension by the actual modulus class map. -/
def modulusPicardOneSheafScalarExtensionIso :
    modulusPicardOneSheaf (baseChange R c R') (modulusBaseChange c i (specMap R R')) ≅
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (specMap R R')).obj
        (modulusPicardOneSheaf c i) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
    (Type (u + 1))).mapIso (modulusPicardOneScalarExtensionIso c i R') ≪≫
      ((Over.map (specMap R R')).pushforwardContinuousSheafificationCompatibility
        (Type (u + 1)) (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).app (modulusPicardOnePresheaf c i)

/-- The sheaf comparison retains the actual scalar-extension class of every rigidified bundle. -/
@[reassoc] theorem toSheafify_modulusPicardOneScalarExtension :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
        (modulusPicardOnePresheaf (baseChange R c R')
          (modulusBaseChange c i (specMap R R'))) ≫
      (modulusPicardOneSheafScalarExtensionIso c i R').hom.hom =
        (modulusPicardOneScalarExtensionIso c i R').hom ≫
          Functor.whiskerLeft (Over.map (specMap R R')).op
            (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
              (modulusPicardOnePresheaf c i)) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let J' := Scheme.fppfTopology.over (Spec (CommRingCat.of R'))
  let F := modulusPicardOnePresheaf c i
  let F' := modulusPicardOnePresheaf (baseChange R c R')
    (modulusBaseChange c i (specMap R R'))
  let a := modulusPicardOneScalarExtensionIso c i R'
  change toSheafify J' F' ≫ (sheafifyMap J' a.hom ≫
      (((Over.map (specMap R R')).pushforwardContinuousSheafificationCompatibility
        (Type (u + 1)) J' J).hom.app F).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    Functor.toSheafify_pullbackSheafificationCompatibility]
  rfl

end AlgebraicGeometry.GeneralizedJacobian
