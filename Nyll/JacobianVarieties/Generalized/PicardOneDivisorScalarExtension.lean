/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardOneModulusIso
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionSheaf

/-! # Picard-one for the actual scalar-extended relative divisor -/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The full divisor, including multiplicities and frames, commutes with intrinsic degree one. -/
def modulusPicardOne_divisorScalarExtensionIso :
    modulusPicardOnePresheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) ≅
      (Over.map (specMap K L)).op ⋙ modulusPicardOnePresheaf c (modulusCurveMap D) :=
  (modulusPicardOneModulusIso (baseChange K c L)
    (divisorScalarExtensionModulusIso D L)
    (divisorScalarExtensionModulusIso_square D L)).symm ≪≫
      modulusPicardOneScalarExtensionIso c (modulusCurveMap D) L

/-- Scalar extension compares the actual divisor's intrinsic degree-one fppf sheaf. -/
def modulusPicardOneSheaf_divisorScalarExtensionIso :
    modulusPicardOneSheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) ≅
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (specMap K L)).obj
        (modulusPicardOneSheaf c (modulusCurveMap D)) :=
  (modulusPicardOneSheafModulusIso (baseChange K c L)
    (divisorScalarExtensionModulusIso D L)
    (divisorScalarExtensionModulusIso_square D L)).symm ≪≫
      modulusPicardOneSheafScalarExtensionIso c (modulusCurveMap D) L

/-- Every rigidified degree-one class is sent by its actual scalar-extension comparison. -/
@[reassoc] theorem toSheafify_modulusPicardOne_divisorScalarExtension :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
        (modulusPicardOnePresheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))) ≫
      (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom =
        (modulusPicardOne_divisorScalarExtensionIso D L).hom ≫
          Functor.whiskerLeft (Over.map (specMap K L)).op
            (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
              (modulusPicardOnePresheaf c (modulusCurveMap D))) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of L))
  let a := modulusPicardOneModulusIso (baseChange K c L)
    (divisorScalarExtensionModulusIso D L) (divisorScalarExtensionModulusIso_square D L)
  let b : sheafify J (modulusPicardOnePresheaf (baseChange K c L)
      (modulusBaseChange c (modulusCurveMap D) (specMap K L))) ⟶
      (Over.map (specMap K L)).op ⋙ (modulusPicardOneSheaf c (modulusCurveMap D)).obj :=
    (modulusPicardOneSheafScalarExtensionIso c (modulusCurveMap D) L).hom.hom
  let η := Functor.whiskerLeft (Over.map (specMap K L)).op
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardOnePresheaf c (modulusCurveMap D)))
  have hb : toSheafify J _ ≫ b =
      (modulusPicardOneScalarExtensionIso c (modulusCurveMap D) L).hom ≫ η :=
    toSheafify_modulusPicardOneScalarExtension c (modulusCurveMap D) L
  change toSheafify J _ ≫ (sheafifyMap J a.inv ≫ b) =
    (a.inv ≫ (modulusPicardOneScalarExtensionIso c (modulusCurveMap D) L).hom) ≫ η
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ b) (toSheafify_naturality J a.inv).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a.inv ≫ f) hb).trans (Category.assoc _ _ _).symm)))

end AlgebraicGeometry.GeneralizedJacobian
