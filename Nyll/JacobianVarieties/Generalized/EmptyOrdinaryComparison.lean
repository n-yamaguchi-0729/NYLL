/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Generalized.UnpointedEmptyConstruction
import Nyll.JacobianVarieties.Generalized.ExistingJacobianGroupScheme
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-!
# Empty modulus agrees with the existing ordinary Jacobian

The comparison is an isomorphism to the previously chosen ordinary Jacobian
with its original tensor-product relative group law. Both sides classify the
actual fppf group sheaves, including when the curve has no rational point.
-/

noncomputable section

universe u

open CategoryTheory NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))

/-- The empty-modulus generalized Jacobian is the existing ordinary Jacobian as a group scheme. -/
def zeroDegreeOrdinaryComparison :
    groupScheme c D ≅ JacobianVarieties.Picard.Unpointed.groupScheme K c :=
  SchemeTheory.RepresentedGroups.iso
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (ordinaryRelativePicardZeroGroupSheaf c).obj
    (Unpointed.zeroDegreeGroupRepresentable c D)
    (JacobianVarieties.Picard.Unpointed.groupSheafRepresentation K c)
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      CommGrpCat.{u + 1}).mapIso (Unpointed.zeroDegreeSheafIso c D)) ≪≫
        JacobianVarieties.Picard.Unpointed.sheafGroupSchemeIso K c

end AlgebraicGeometry.GeneralizedJacobian
