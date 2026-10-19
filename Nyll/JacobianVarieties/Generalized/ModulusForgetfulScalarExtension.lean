/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedGroupBaseChange
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionSheaf
import Nyll.JacobianVarieties.Generalized.PicardZeroForgetfulGroup

/-! # The actual forgetful square under scalar extension -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- Forgetting the actual rigidification commutes with the actual pullback of the line bundle. -/
theorem forgetModulusZeroGroupPresheaf_scalarExtension :
    (modulusPicardZeroGroupScalarExtensionIso c i R').hom ≫
        Functor.whiskerLeft (Over.map (specMap R R')).op
          (forgetModulusZeroGroupPresheaf c i) =
      forgetModulusZeroGroupPresheaf (baseChange R c R')
          (modulusBaseChange c i (specMap R R')) ≫
        (Unrigidified.zeroCommGrpBaseChangeIso c R').hom := by
  ext T x
  rcases x with ⟨x, hx⟩
  apply Subtype.ext
  induction x using Quotient.ind with
  | _ M => rfl

/-- The ordinary Picard-zero group sheaf commutes with scalar extension through actual bundles. -/
def ordinaryZeroGroupSheafScalarExtensionIso :
    ordinaryRelativePicardZeroGroupSheaf (baseChange R c R') ≅
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap R R')).obj
        (ordinaryRelativePicardZeroGroupSheaf c) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
    CommGrpCat.{u + 1}).mapIso (Unrigidified.zeroCommGrpBaseChangeIso c R') ≪≫
      ((Over.map (specMap R R')).pushforwardContinuousSheafificationCompatibility
        CommGrpCat.{u + 1} (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).app
          (Unrigidified.zeroCommGrpPresheaf c)

/-- The forgetful square commutes after actual fppf sheafification. -/
theorem forgetModulusZeroGroupSheaf_scalarExtension :
    (modulusPicardZeroGroupSheafScalarExtensionIso c i R').hom ≫
        (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap R R')).map
          (forgetModulusZeroGroupSheaf c i) =
      forgetModulusZeroGroupSheaf (baseChange R c R')
          (modulusBaseChange c i (specMap R R')) ≫
        (ordinaryZeroGroupSheafScalarExtensionIso c R').hom := by
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
    CommGrpCat.{u + 1}
  let e := (Over.map (specMap R R')).pushforwardContinuousSheafificationCompatibility
    CommGrpCat.{u + 1} (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
  have hn := e.hom.naturality (forgetModulusZeroGroupPresheaf c i)
  change (S.map (modulusPicardZeroGroupScalarExtensionIso c i R').hom ≫
      e.hom.app (modulusPicardZeroGroupPresheaf c i)) ≫
        ((presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          CommGrpCat.{u + 1}) ⋙
          (Over.map (specMap R R')).sheafPushforwardContinuous CommGrpCat.{u + 1}
            (Scheme.fppfTopology.over (Spec (CommRingCat.of R')))
            (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map
              (forgetModulusZeroGroupPresheaf c i) =
    S.map (forgetModulusZeroGroupPresheaf (baseChange R c R')
      (modulusBaseChange c i (specMap R R'))) ≫
        (S.map (Unrigidified.zeroCommGrpBaseChangeIso c R').hom ≫
          e.hom.app (Unrigidified.zeroCommGrpPresheaf c))
  rw [Category.assoc, ← hn, ← Category.assoc]
  change (S.map (modulusPicardZeroGroupScalarExtensionIso c i R').hom ≫
      S.map (Functor.whiskerLeft (Over.map (specMap R R')).op
        (forgetModulusZeroGroupPresheaf c i))) ≫
      e.hom.app (Unrigidified.zeroCommGrpPresheaf c) = _
  rw [← S.map_comp, forgetModulusZeroGroupPresheaf_scalarExtension,
    S.map_comp, Category.assoc]

variable {D' : Scheme.{u}} {i' : D' ⟶ C} (a : D' ≅ D) (w : i' = a.hom ≫ i)

/-- An actual whole-modulus isomorphism leaves the underlying relative class unchanged. -/
theorem forgetModulusZeroGroupPresheaf_modulusIso :
    (modulusPicardZeroGroupModulusIso c a w).hom ≫
      forgetModulusZeroGroupPresheaf c i' = forgetModulusZeroGroupPresheaf c i := by
  ext T x
  apply Subtype.ext
  exact modulusIsoClassesEquiv_forget c a w T.unop.hom x.val

/-- The same compatibility for the actual sheaves. -/
theorem forgetModulusZeroGroupSheaf_modulusIso :
    (modulusPicardZeroGroupSheafModulusIso c a w).hom ≫
      forgetModulusZeroGroupSheaf c i' = forgetModulusZeroGroupSheaf c i := by
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}
  change S.map (modulusPicardZeroGroupModulusIso c a w).hom ≫
    S.map (forgetModulusZeroGroupPresheaf c i') = S.map (forgetModulusZeroGroupPresheaf c i)
  rw [← S.map_comp, forgetModulusZeroGroupPresheaf_modulusIso]

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- Forgetting commutes with the comparison for the actual scalar-extended relative divisor. -/
theorem forgetModulusZeroGroupSheaf_divisorScalarExtension :
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom ≫
        (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
          (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) =
      forgetModulusZeroGroupSheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) ≫
        (ordinaryZeroGroupSheafScalarExtensionIso c L).hom := by
  let a := modulusPicardZeroGroupSheafModulusIso (baseChange K c L)
    (divisorScalarExtensionModulusIso D L) (divisorScalarExtensionModulusIso_square D L)
  have ha : a.inv ≫ forgetModulusZeroGroupSheaf (baseChange K c L)
      (modulusBaseChange c (modulusCurveMap D) (specMap K L)) =
    forgetModulusZeroGroupSheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) :=
    a.inv_comp_eq.mpr (forgetModulusZeroGroupSheaf_modulusIso (baseChange K c L)
      (modulusBaseChange c (modulusCurveMap D) (specMap K L))
      (divisorScalarExtensionModulusIso D L) (divisorScalarExtensionModulusIso_square D L)).symm
  change (a.inv ≫ (modulusPicardZeroGroupSheafScalarExtensionIso c (modulusCurveMap D) L).hom)
    ≫ _ = _
  rw [Category.assoc, forgetModulusZeroGroupSheaf_scalarExtension, ← Category.assoc, ha]

end AlgebraicGeometry.GeneralizedJacobian
