/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareRawSurjectivity
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local surjectivity of the total Poincaré frame comparison

The already constructed comparison commutes with passage from actual frames and
modulus classes to their fppf sheaves. Its local surjectivity follows from actual
local Poincaré classification, rather than an extra representability or lifting
assumption. This does not yet identify the comparison as an isomorphism.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open SchemeTheory.WeilRestriction AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

/-- Relative and absolute sheafification give the same actual modulus zero class. -/
theorem poincareRawToFrameFamily_comp_toModulusPicardZero :
    poincareRawToFrameFamily D h ≫ poincareFrameTotalToModulusPicardZero D h =
      poincareRawFrameToModulusZero D h ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D)) := by
  let a := modulusFramesToPicardZero D J.toBase h.poincare.isInvertible
    (poincareUnderlying_fibrewiseZero h)
  have hrel :
      toScalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase)
          (poincareModulusBundle D h) ≫
        (modulusFrameSheafToPicardZero D J.toBase h.poincare.isInvertible
          (poincareUnderlying_fibrewiseZero h)).hom =
      a ≫ Functor.whiskerLeft (Over.map J.toBase).op
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))) := by
    change toSheafify (Scheme.fppfTopology.over J.P) _ ≫
      (sheafifyMap (Scheme.fppfTopology.over J.P) a ≫ _) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
    exact congrArg (fun m => a ≫ m)
      (Functor.toSheafify_pullbackSheafificationCompatibility
        (Over.map J.toBase) (Type (u + 1)) (Scheme.fppfTopology.over J.P)
        (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D)))
  ext T x
  let e := (relativeTotalForgetIso J.toBase).inv.app (Over.mk x.1)
  have hx := ConcreteCategory.congr_hom
    (NatTrans.congr_app hrel (op (Over.mk x.1.left))) x.2
  change (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map e.op
      ((toScalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase)
          (poincareModulusBundle D h) ≫
        (modulusFrameSheafToPicardZero D J.toBase h.poincare.isInvertible
          (poincareUnderlying_fibrewiseZero h)).hom).app (op (Over.mk x.1.left)) x.2) =
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))).app T
        ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map e.op
          (a.app (op (Over.mk x.1.left)) x.2))
  rw [hx]
  exact ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (modulusPicardZeroPresheaf c (modulusCurveMap D))).naturality_apply e.op
      (a.app (op (Over.mk x.1.left)) x.2)).symm

/-- Every modulus Picard-zero sheaf section is fppf locally supplied by the
constructed total Poincaré frame family. -/
instance poincareFrameTotalToModulusPicardZero_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareFrameTotalToModulusPicardZero D h) := by
  have : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawToFrameFamily D h ≫ poincareFrameTotalToModulusPicardZero D h) := by
    rw [poincareRawToFrameFamily_comp_toModulusPicardZero D h]
    exact Presheaf.isLocallySurjective_comp
      (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawFrameToModulusZero D h)
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D)))
  exact Presheaf.isLocallySurjective_of_isLocallySurjective
    (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (poincareRawToFrameFamily D h) (poincareFrameTotalToModulusPicardZero D h)

end AlgebraicGeometry.GeneralizedJacobian
