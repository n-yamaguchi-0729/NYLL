/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelOneFamily
import Nyll.JacobianVarieties.Generalized.PicardOneUnpointedConstruction

/-! # The intrinsic Abel morphism over an arbitrary field, without a rational point -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual point family classifies a morphism into the descended Picard-one scheme. -/
def abelOneMap :
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ picardOne c D :=
  (picardOneRepresentable c D).homEquiv.symm
    ((modulusAbelOneSheafMap c (modulusCurveMap D)).app
      (op (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))) (ULift.up (𝟙 _)))

/-- On every test scheme, this morphism is the original canonically rigidified point class. -/
theorem abelOneMap_classifies {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (picardOneRepresentable c D).homEquiv (x ≫ abelOneMap c D) =
      (modulusAbelOneSheafMap c (modulusCurveMap D)).app (op T) (ULift.up x) := by
  rw [(picardOneRepresentable c D).homEquiv_comp]
  change (modulusPicardOneSheaf c (modulusCurveMap D)).obj.map x.op
      ((picardOneRepresentable c D).homEquiv
        ((picardOneRepresentable c D).homEquiv.symm _)) = _
  rw [Equiv.apply_symm_apply]
  let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
  let a : ULift.{u + 1} (U ⟶ U) := ULift.up (𝟙 U)
  have h := (modulusAbelOneSheafMap c (modulusCurveMap D)).naturality_apply x.op a
  change (modulusAbelOneSheafMap c (modulusCurveMap D)).app (op T)
    (ULift.up (x ≫ 𝟙 _)) = _ at h
  rw [Category.comp_id] at h
  exact h.symm

end AlgebraicGeometry.GeneralizedJacobian
