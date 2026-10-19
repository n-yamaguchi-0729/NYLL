/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusTransitionScalarExtensionSheaf
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupSchemeMap
import Nyll.JacobianVarieties.Generalized.ModulusTransition
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupBaseChange

/-! # Scalar extension of the actual generalized-Jacobian group transitions -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)

/-- The actual transition has the canonical represented underlying morphism. -/
theorem transitionAlong_hom :
    (transitionAlong c D D' j w).hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism
        (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
        (modulusPicardZeroGroupSheaf c (modulusCurveMap D')).obj
        (groupRepresentable c D) (groupRepresentable c D')
        (modulusRestrictionZeroSheaf c j w).hom := by
  cases d <;> cases d' <;> rfl

variable (L : Type u) [Field L] [Algebra K L]

/-- Restriction of the same transition on the actual pulled-back group carriers. -/
def transitionAlongScalarExtension : groupScalarExtension c D L ⟶ groupScalarExtension c D' L :=
  SchemeTheory.RepresentedGroups.map
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D')).obj)
    (groupScalarExtensionRepresentable c D L) (groupScalarExtensionRepresentable c D' L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusRestrictionZeroSheaf c j w).hom)

/-- This is the actual scheme pullback of the transition, including its group law. -/
theorem transitionAlongScalarExtension_eq :
    (transitionAlongScalarExtension c D D' j w L).hom.hom.hom =
      (Over.pullback (specMap K L)).map (transitionAlong c D D' j w).hom.hom.hom := by
  exact (SchemeTheory.RepresentedGroups.mapMorphism_baseChange (specMap K L)
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D')).obj
    (groupRepresentable c D) (groupRepresentable c D')
    (modulusRestrictionZeroSheaf c j w).hom).trans
      (congrArg (Over.pullback (specMap K L)).map (transitionAlong_hom c D D' j w).symm)

/-- The canonical group-scheme scalar comparisons preserve the actual modulus transition. -/
theorem transitionAlong_scalarExtension_square :
    (groupScalarExtensionIso c D L).hom ≫
        transitionAlong (baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)) (D'.changeBaseOfIdentity (specMap K L))
          (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L) =
      transitionAlongScalarExtension c D D' j w L ≫ (groupScalarExtensionIso c D' L).hom := by
  have hs := congrArg (fun m :
    (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).obj
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)) ⟶
    modulusPicardZeroGroupSheaf (baseChange K c L)
      (modulusCurveMap (D'.changeBaseOfIdentity (specMap K L))) => m.hom)
    (modulusRestrictionZeroSheaf_divisorScalarExtension_inv D D' j w L)
  have h := SchemeTheory.RepresentedGroups.mapMorphism_square
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D')).obj)
    (modulusPicardZeroGroupSheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj
    (modulusPicardZeroGroupSheaf (baseChange K c L)
      (modulusCurveMap (D'.changeBaseOfIdentity (specMap K L)))).obj
    (groupScalarExtensionRepresentable c D L) (groupScalarExtensionRepresentable c D' L)
    (groupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))
    (groupRepresentable (baseChange K c L) (D'.changeBaseOfIdentity (specMap K L)))
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv.hom
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D' L).inv.hom
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusRestrictionZeroSheaf c j w).hom)
    (modulusRestrictionZeroSheaf (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
      (divisorRestrictionScalarMap_square D D' j w L)).hom hs
  apply CommGrp.hom_ext
  exact (congrArg₂ (fun f g => f ≫ g) (groupScalarExtensionIso_hom c D L)
    (transitionAlong_hom (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) (D'.changeBaseOfIdentity (specMap K L))
      (divisorRestrictionScalarMap D D' j w L)
      (divisorRestrictionScalarMap_square D D' j w L))).trans
        (h.trans (congrArg (fun f => (transitionAlongScalarExtension c D D' j w L).hom.hom.hom ≫ f)
          (groupScalarExtensionIso_hom c D' L).symm))

end AlgebraicGeometry.GeneralizedJacobian
