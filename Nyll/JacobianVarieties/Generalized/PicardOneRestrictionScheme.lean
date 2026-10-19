/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneRestriction
import Nyll.JacobianVarieties.Generalized.ModulusAbelOneMap

/-! # Actual degree-one scheme transitions and the intrinsic Abel square -/

noncomputable section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem representableAbelSquare {B : Type u} [Category.{v} B]
    {F G : Bᵒᵖ ⥤ Type (max w v)} {X Y U V : B}
    (eF : F.RepresentableBy X) (eG : G.RepresentableBy Y)
    (A : uliftYoneda.{w}.obj U ⟶ F) (A' : uliftYoneda.{w}.obj V ⟶ G)
    (r : F ⟶ G) (f : U ⟶ V) (a : U ⟶ X) (b : V ⟶ Y) (t : X ⟶ Y)
    (ha : ∀ {T} (x : T ⟶ U), eF.homEquiv (x ≫ a) = A.app (op T) (ULift.up x))
    (hb : ∀ {T} (x : T ⟶ V), eG.homEquiv (x ≫ b) = A'.app (op T) (ULift.up x))
    (ht : ∀ {T} (x : T ⟶ X), eG.homEquiv (x ≫ t) = r.app (op T) (eF.homEquiv x))
    (hs : A ≫ r = uliftYoneda.map f ≫ A') : a ≫ t = f ≫ b := by
  let z : ULift.{w} (U ⟶ U) := ULift.up (𝟙 U)
  have hA : eF.homEquiv a = A.app (op U) z :=
    (congrArg eF.homEquiv (Category.id_comp a)).symm.trans (ha (𝟙 U))
  have hS : r.app (op U) (A.app (op U) z) = A'.app (op U) (ULift.up f) := by
    have h := congrArg (fun q : uliftYoneda.{w}.obj U ⟶ G => q.app (op U) z) hs
    change r.app (op U) (A.app (op U) z) = A'.app (op U) (ULift.up (𝟙 U ≫ f)) at h
    exact h.trans (congrArg (fun q => A'.app (op U) (ULift.up q)) (Category.id_comp f))
  exact eG.homEquiv.injective
    ((ht a).trans ((congrArg (r.app (op U)) hA).trans (hS.trans (hb f).symm)))

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)

/-- The morphism representing restriction of the actual degree-one rigidification. -/
def picardOneTransitionAlong : picardOne c D ⟶ picardOne c D' :=
  (picardOneRepresentable c D').homEquiv.symm
    ((modulusRestrictionOneSheaf c j w).hom.app (op (picardOne c D))
      ((picardOneRepresentable c D).homEquiv (𝟙 _)))

/-- Every test point classifies its actual restricted degree-one frame. -/
theorem picardOneTransitionAlong_classifies {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ picardOne c D) :
    (picardOneRepresentable c D').homEquiv (x ≫ picardOneTransitionAlong c D D' j w) =
      (modulusRestrictionOneSheaf c j w).hom.app (op T)
        ((picardOneRepresentable c D).homEquiv x) := by
  rw [(picardOneRepresentable c D').homEquiv_comp]
  change (modulusPicardOneSheaf c (modulusCurveMap D')).obj.map x.op
    ((picardOneRepresentable c D').homEquiv ((picardOneRepresentable c D').homEquiv.symm _)) = _
  rw [Equiv.apply_symm_apply]
  have h := (modulusRestrictionOneSheaf c j w).hom.naturality_apply x.op
    ((picardOneRepresentable c D).homEquiv (𝟙 _))
  exact h.symm.trans (congrArg ((modulusRestrictionOneSheaf c j w).hom.app (op T))
    (((picardOneRepresentable c D).homEquiv_comp x (𝟙 _)).symm.trans
      (congrArg (picardOneRepresentable c D).homEquiv (Category.comp_id x))))

/-- The intrinsic Abel morphisms commute with the actual scheme transition. -/
theorem abelOneMap_transitionAlong :
    abelOneMap c D ≫ picardOneTransitionAlong c D D' j w =
      modulusComplementRestriction c j w ≫ abelOneMap c D' := by
  exact representableAbelSquare (picardOneRepresentable c D) (picardOneRepresentable c D')
    (modulusAbelOneSheafMap c (modulusCurveMap D))
    (modulusAbelOneSheafMap c (modulusCurveMap D'))
    (modulusRestrictionOneSheaf c j w).hom (modulusComplementRestriction c j w)
    (abelOneMap c D) (abelOneMap c D') (picardOneTransitionAlong c D D' j w)
    (abelOneMap_classifies c D) (abelOneMap_classifies c D')
    (picardOneTransitionAlong_classifies c D D' j w)
    (modulusAbelOneSheafMap_restriction c j w)

end AlgebraicGeometry.GeneralizedJacobian
