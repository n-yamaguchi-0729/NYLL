/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroZariski
import Nyll.JacobianVarieties.Generalized.EmptyPicardZeroZariski

/-! # Actual affine representatives of the modulus Picard-zero sheaf in every degree -/

noncomputable section

universe u

open CategoryTheory Opposite NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

include ε in
/-- The original sheafification admits actual rigidified representatives in the Zariski topology,
for every degree of the full modulus, including zero. -/
theorem pointed_modulusPicardZero_toSheafify_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D))) := by
  cases d with
  | zero => exact zeroDegree_modulusPicardZero_toSheafify_isLocallySurjective_zariski c ε D
  | succ n => exact modulusPicardZero_toSheafify_isLocallySurjective_zariski c ε D (Nat.succ_pos n)

include ε in
/-- Every actual zero-sheaf family has specified actual rigidified bundles on an affine open cover.
The positive-degree cover is constructed by norm charts; degree zero uses
the ordinary Poincare family. -/
theorem pointed_modulusPicardZero_exists_affineOpenCover_bundles
    (T : Over (Spec (CommRingCat.of K)))
    (x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)) :
    ∃ U : Scheme.AffineOpenCover.{u, u} T.left, ∀ j,
      ∃ (M : RigidifiedLineBundle
          (modulusBaseChange c (modulusCurveMap D) (U.f j ≫ T.hom)))
        (hM : RigidifiedLineBundle.classOf M ∈
          (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
            (op (Over.mk (U.f j ≫ T.hom)))),
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
            (op (Over.mk (U.f j ≫ T.hom))) ⟨RigidifiedLineBundle.classOf M, hM⟩ =
          (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map
            (Over.homMk (U.f j) : Over.mk (U.f j ≫ T.hom) ⟶ T).op x := by
  cases d with
  | zero => exact zeroDegree_modulusPicardZero_exists_affineOpenCover_bundles c ε D T x
  | succ n => exact modulusPicardZero_exists_affineOpenCover_bundles c ε D (Nat.succ_pos n) T x

end AlgebraicGeometry.GeneralizedJacobian
