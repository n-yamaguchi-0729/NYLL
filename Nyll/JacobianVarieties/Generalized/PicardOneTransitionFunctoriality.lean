/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneRestrictionScheme
import Nyll.JacobianVarieties.Generalized.PicardOneRestrictionAction
import Nyll.JacobianVarieties.Generalized.PicardOneModuleObject
import Nyll.JacobianVarieties.Generalized.ModulusTransition

/-! # Actual degree-one torsor transitions, their composition, and equivariance -/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)

/-- Restricting a degree-one torsor to the same modulus gives the identity morphism. -/
theorem picardOneTransitionAlong_id :
    picardOneTransitionAlong c D D (𝟙 _) (Category.id_comp (modulusCurveMap D)).symm =
      𝟙 (picardOne c D) := by
  apply (picardOneRepresentable c D).homEquiv.injective
  have h := picardOneTransitionAlong_classifies c D D (𝟙 _)
    (Category.id_comp (modulusCurveMap D)).symm (𝟙 (picardOne c D))
  rw [Category.id_comp, modulusRestrictionOneSheaf_id] at h
  exact h

/-- Successive degree-one transitions restrict the actual frame along the composite inclusion. -/
theorem picardOneTransitionAlong_comp {d'' : ℕ}
    (D'' : RelEffCartierDiv c d'' (𝟙 (Spec (CommRingCat.of K))))
    (k : D''.I.subscheme ⟶ D'.I.subscheme)
    (w' : modulusCurveMap D'' = k ≫ modulusCurveMap D') :
    picardOneTransitionAlong c D D' j w ≫ picardOneTransitionAlong c D' D'' k w' =
      picardOneTransitionAlong c D D'' (k ≫ j) (by rw [w', w, Category.assoc]) := by
  apply (picardOneRepresentable c D'').homEquiv.injective
  rw [picardOneTransitionAlong_classifies]
  have h₁ := picardOneTransitionAlong_classifies c D D' j w (𝟙 (picardOne c D))
  have h₂ := picardOneTransitionAlong_classifies c D D'' (k ≫ j)
    (by rw [w', w, Category.assoc]) (𝟙 (picardOne c D))
  rw [Category.id_comp] at h₁ h₂
  rw [h₁, h₂]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun a => a.hom) (modulusRestrictionOneSheaf_comp c j w k w'))
      (op (picardOne c D))) ((picardOneRepresentable c D).homEquiv (𝟙 _))

/-- The intrinsic degree-one transition is equivariant for the actual generalized Jacobian map. -/
theorem picardOneTransitionAlong_smul {T : Over (Spec (CommRingCat.of K))}
    (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D) :
    (g • x) ≫ picardOneTransitionAlong c D D' j w =
      (g ≫ (transitionAlong c D D' j w).hom.hom.hom) •
        (x ≫ picardOneTransitionAlong c D D' j w) := by
  apply (picardOneRepresentable c D').homEquiv.injective
  change (picardOneRepresentable c D').homEquiv
    ((lift g x ≫ picardOneTensorAction c D) ≫ picardOneTransitionAlong c D D' j w) =
      (picardOneRepresentable c D').homEquiv
        (lift (g ≫ (transitionAlong c D D' j w).hom.hom.hom)
          (x ≫ picardOneTransitionAlong c D D' j w) ≫ picardOneTensorAction c D')
  rw [picardOneTransitionAlong_classifies, picardOneTensorAction_classifies,
    picardOneTensorAction_classifies, transitionAlong_homEquiv,
    picardOneTransitionAlong_classifies]
  exact modulusRestrictionOneSheaf_action c j w T
    ((groupRepresentable c D).homEquiv g) ((picardOneRepresentable c D).homEquiv x)

/-- Ideal containment supplies the canonical degree-one torsor transition. -/
def picardOneTransition (h : D.I ≤ D'.I) : picardOne c D ⟶ picardOne c D' :=
  picardOneTransitionAlong c D D' (Scheme.IdealSheafData.inclusion h)
    (modulusIdealInclusion_curve c D D' h)

/-- The canonical ideal-containment transition retains the actual intrinsic Abel square. -/
theorem abelOneMap_transition (h : D.I ≤ D'.I) :
    abelOneMap c D ≫ picardOneTransition c D D' h =
      modulusComplementRestriction c (Scheme.IdealSheafData.inclusion h)
        (modulusIdealInclusion_curve c D D' h) ≫ abelOneMap c D' :=
  abelOneMap_transitionAlong c D D' (Scheme.IdealSheafData.inclusion h)
    (modulusIdealInclusion_curve c D D' h)

end AlgebraicGeometry.GeneralizedJacobian
