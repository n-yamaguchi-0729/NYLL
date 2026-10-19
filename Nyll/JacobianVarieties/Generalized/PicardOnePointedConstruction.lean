/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelOneFamily
import Nyll.JacobianVarieties.Generalized.Construction

/-!
# Actual representation and Abel map for Picard-one with a selected open-curve point

The target sheaf is defined without a basepoint. A point of the open complement
supplies the proved tensor translation that represents it on the constructed
Jacobian carrier. The Abel map classifies the original point class, rather than
an assumed degree-one family or an abstractly labelled torsor.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))

/-- An actual open-curve point supplies a representation of the intrinsic Picard-one sheaf. -/
def picardOnePointedRepresentable :
    (modulusPicardOneSheaf c (modulusCurveMap D)).obj.RepresentableBy (groupScheme c D).X :=
  (picardZeroRepresentable c D).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (Type (u + 1))).mapIso (modulusPicardOneTranslationSheafIso c (modulusCurveMap D) ε))

/-- The actual Abel morphism into the carrier representing intrinsic Picard-one. -/
def modulusAbelOneMap :
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ (groupScheme c D).X :=
  (picardOnePointedRepresentable c D ε).homEquiv.symm
    ((modulusAbelOneSheafMap c (modulusCurveMap D)).app
      (op (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))) (ULift.up (𝟙 _)))

/-- This morphism classifies the actual degree-one point family on every test scheme. -/
theorem modulusAbelOneMap_classifies {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (picardOnePointedRepresentable c D ε).homEquiv (x ≫ modulusAbelOneMap c D ε) =
      (modulusAbelOneSheafMap c (modulusCurveMap D)).app (op T) (ULift.up x) := by
  rw [(picardOnePointedRepresentable c D ε).homEquiv_comp]
  change (modulusPicardOneSheaf c (modulusCurveMap D)).obj.map x.op
      ((picardOnePointedRepresentable c D ε).homEquiv
        ((picardOnePointedRepresentable c D ε).homEquiv.symm _)) = _
  rw [Equiv.apply_symm_apply]
  let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
  let a : ULift.{u + 1} (U ⟶ U) := ULift.up (𝟙 U)
  have h := (modulusAbelOneSheafMap c (modulusCurveMap D)).naturality_apply x.op a
  change (modulusAbelOneSheafMap c (modulusCurveMap D)).app (op T) (ULift.up (x ≫ 𝟙 _)) = _ at h
  rw [Category.comp_id] at h
  exact h.symm

end AlgebraicGeometry.GeneralizedJacobian
