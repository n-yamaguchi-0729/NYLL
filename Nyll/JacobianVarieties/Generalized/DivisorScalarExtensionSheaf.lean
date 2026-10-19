/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusIsoGroupSheaf
import Nyll.JacobianVarieties.Generalized.ModulusScalarExtensionSheaf

/-! # The Picard-zero sheaf of the actual scalar-extended divisor -/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- Scalar extension compares the actual relative divisor's Picard-zero group sheaf
with the restriction of the original sheaf, without discarding multiplicities. -/
def modulusPicardZeroGroupSheaf_divisorScalarExtensionIso :
    modulusPicardZeroGroupSheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) ≅
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).obj
        (modulusPicardZeroGroupSheaf c (modulusCurveMap D)) :=
  (modulusPicardZeroGroupSheafModulusIso (baseChange K c L)
    (divisorScalarExtensionModulusIso D L) (divisorScalarExtensionModulusIso_square D L)).symm ≪≫
      modulusPicardZeroGroupSheafScalarExtensionIso c (modulusCurveMap D) L

end AlgebraicGeometry.GeneralizedJacobian
