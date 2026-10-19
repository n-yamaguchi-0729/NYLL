/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupScheme
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupDiagram

/-! # The actual morphism underlying the group scalar-extension comparison -/

noncomputable section
universe u
open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- An explicit formula separates the actual scalar-extension morphism from its group data. -/
theorem groupScalarExtensionIso_hom :
    (groupScalarExtensionIso c D L).hom.hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism
        ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
        (modulusPicardZeroGroupSheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj
        (groupScalarExtensionRepresentable c D L)
        (groupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))
        (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv.hom := by
  cases d <;> rfl

/-- The native pullback group comparison has the same underlying morphism
as the existing represented full-modulus comparison. -/
theorem groupActualScalarExtensionIso_hom :
    (groupActualScalarExtensionIso c D L).hom.hom.hom.hom =
      (groupScalarExtensionIso c D L).hom.hom.hom.hom := by
  cases d
  all_goals
    let e := groupScalarExtensionRepresentable c D L
    have he : (e.uniqueUpToIso e).inv = 𝟙 _ := by
      change e.homEquiv.symm (e.homEquiv (𝟙 _)) = 𝟙 _
      exact e.homEquiv.symm_apply_apply _
    change (e.uniqueUpToIso e).inv ≫
      (groupScalarExtensionIso c D L).hom.hom.hom.hom = _
    exact (congrArg (fun f => f ≫
      (groupScalarExtensionIso c D L).hom.hom.hom.hom) he).trans
        (Category.id_comp _)

end AlgebraicGeometry.GeneralizedJacobian
