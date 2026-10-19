/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneModuleObject
import Nyll.JacobianVarieties.Generalized.ModulusAbelMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelOneMap

/-! # The pointed Abel class is the actual difference in the intrinsic Picard-one torsor -/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))

/-- The point-minus-basepoint class acts on the actual basepoint line bundle by tensor product. -/
theorem modulusAbelZeroClass_action {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    modulusPicardOneAction c (modulusCurveMap D) T
        (modulusAbelZeroClass c (modulusCurveMap D) ε x)
        ((modulusAbelOnePresheafMap c (modulusCurveMap D)).app (op T)
          (ULift.up ((Over.homMk T.hom (Category.comp_id T.hom) :
            T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε))) =
      (modulusAbelOnePresheafMap c (modulusCurveMap D)).app (op T) (ULift.up x) := by
  let i := modulusCurveMap D
  let p : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk T.hom (Category.comp_id T.hom)
  let b := modulusGroundClass c i
    (modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of K)))) ε) T
  have hb : b = modulusAbelPointClass c i (T := T) (p ≫ ε) :=
    modulusGroundClass_abel c i ε T
  apply Subtype.ext
  change (modulusAbelPointClass c i (T := T) x / b) *
    modulusAbelPointClass c i (T := T) (p ≫ ε) = modulusAbelPointClass c i (T := T) x
  rw [← hb]
  exact div_mul_cancel _ _

/-- The pointed Abel map is the canonical group element carrying the basepoint to the point. -/
theorem modulusAbelMap_smul_basepoint {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (x ≫ modulusAbelMap c D ε) •
        (((Over.homMk T.hom (Category.comp_id T.hom) :
          T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε) ≫ abelOneMap c D) =
      x ≫ abelOneMap c D := by
  let i := modulusCurveMap D
  let p : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk T.hom (Category.comp_id T.hom)
  let g : (modulusPicardZeroGroupPresheaf c i).obj (op T) :=
    modulusAbelZeroClass c i ε x
  let y : (modulusPicardOnePresheaf c i).obj (op T) :=
    (modulusAbelOnePresheafMap c i).app (op T) (ULift.up (p ≫ ε))
  let etaOne := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (modulusPicardOnePresheaf c i)
  apply (picardOneRepresentable c D).homEquiv.injective
  change (picardOneRepresentable c D).homEquiv
    (lift (x ≫ modulusAbelMap c D ε) ((p ≫ ε) ≫ abelOneMap c D) ≫
      picardOneTensorAction c D) = _
  exact (picardOneTensorAction_classifies c D _ _).trans
    ((congrArg₂ (modulusPicardOneIntrinsicAction c i T)
      (modulusAbelMap_classifies c D ε x) (abelOneMap_classifies c D (p ≫ ε))).trans
        ((modulusPicardOneIntrinsicAction_actual c i T g y).trans
          ((congrArg (etaOne.app (op T)) (modulusAbelZeroClass_action c D ε x)).trans
            (abelOneMap_classifies c D x).symm)))

end AlgebraicGeometry.GeneralizedJacobian
