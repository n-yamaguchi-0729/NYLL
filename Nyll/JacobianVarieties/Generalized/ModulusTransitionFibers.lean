/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusTransitionGeometry
import Nyll.JacobianVarieties.Generalized.GroupProjectionConnected

/-! # Uniform transition geometry, including the empty modulus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The empty-target transition has precisely the geometry of the actual forgetting map. -/
private theorem transitionAlong_empty_property
    (D₀ : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))
    (j : D₀.I.subscheme ⟶ D.I.subscheme)
    (w : modulusCurveMap D₀ = j ≫ modulusCurveMap D)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : P (groupProjection c D).hom.hom.hom.left) :
    P (transitionAlong c D D₀ j w).hom.hom.hom.left := by
  let e : (groupScheme c D₀).X.left ≅ (ordinaryGroupScheme c).X.left :=
    (CommGrp.forget _ ⋙ Over.forget _).mapIso (emptyModulusGroupIso c D₀)
  have : IsIso e.hom := e.isIso_hom
  have hs : (transitionAlong c D D₀ j w).hom.hom.hom.left ≫ e.hom =
      (groupProjection c D).hom.hom.hom.left :=
    congrArg Over.Hom.left (transitionAlong_groupProjection c D D₀ j w)
  apply (P.cancel_right_of_respectsIso (transitionAlong c D D₀ j w).hom.hom.hom.left e.hom).mp
  rw [hs]
  exact hP

variable (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D) [IsClosedImmersion j]

/-- Restriction to any smaller effective modulus is smooth on the actual constructed groups. -/
theorem transitionAlong_smooth : Smooth (transitionAlong c D D' j w).hom.hom.hom.left := by
  cases d' with
  | zero =>
      have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
        smooth_isStableUnderBaseChange.respectsIso
      exact transitionAlong_empty_property c D D' j w (@Smooth) (groupProjection_smooth c D)
  | succ n =>
      have hd := Nat.lt_of_lt_of_le (Nat.zero_lt_succ n)
        (modulusDegree_le_of_inclusion D D' j w)
      exact transitionAlong_smooth_of_pos c D D' j w hd (Nat.zero_lt_succ n)

/-- The canonical changing-modulus transition is surjective, also for empty target modulus. -/
theorem transitionAlong_surjective :
    Surjective (transitionAlong c D D' j w).hom.hom.hom.left := by
  cases d' with
  | zero =>
      exact transitionAlong_empty_property c D D' j w (@Surjective)
        (groupProjection_surjective c D)
  | succ n =>
      have hd := Nat.lt_of_lt_of_le (Nat.zero_lt_succ n)
        (modulusDegree_le_of_inclusion D D' j w)
      exact transitionAlong_surjective_of_pos c D D' j w hd (Nat.zero_lt_succ n)

/-- All geometric fibres of actual changing-modulus transitions are connected. -/
theorem transitionAlong_geometricallyConnected :
    GeometricallyConnected (transitionAlong c D D' j w).hom.hom.hom.left := by
  cases d' with
  | zero =>
      have hbc : MorphismProperty.IsStableUnderBaseChange
          (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
        GeometricallyConnected.eq_geometrically ▸ inferInstance
      have : MorphismProperty.RespectsIso
          (@GeometricallyConnected : MorphismProperty Scheme.{u}) := hbc.respectsIso
      exact transitionAlong_empty_property c D D' j w (@GeometricallyConnected)
        (groupProjection_geometricallyConnected c D)
  | succ n =>
      have hd := Nat.lt_of_lt_of_le (Nat.zero_lt_succ n)
        (modulusDegree_le_of_inclusion D D' j w)
      exact transitionAlong_geometricallyConnected_of_pos c D D' j w hd (Nat.zero_lt_succ n)

omit [IsClosedImmersion j] in
/-- The actual scheme-theoretic identity fibre of a canonical modulus transition. -/
def transitionKernelScheme : Over (Spec (CommRingCat.of K)) :=
  Over.mk (pullback.snd (transitionAlong c D D' j w).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme c D').X).left)

/-- The actual kernel scheme is smooth over the original field. -/
theorem transitionKernelScheme_smooth : Smooth (transitionKernelScheme c D D' j w).hom := by
  have : Smooth (transitionAlong c D D' j w).hom.hom.hom.left :=
    transitionAlong_smooth c D D' j w
  change Smooth (pullback.snd (transitionAlong c D D' j w).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme c D').X).left)
  infer_instance

/-- The actual transition kernel is geometrically connected, not merely connected on points. -/
theorem transitionKernelScheme_geometricallyConnected :
    GeometricallyConnected (transitionKernelScheme c D D' j w).hom := by
  have : GeometricallyConnected (transitionAlong c D D' j w).hom.hom.hom.left :=
    transitionAlong_geometricallyConnected c D D' j w
  change GeometricallyConnected (pullback.snd (transitionAlong c D D' j w).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme c D').X).left)
  infer_instance

omit [IsClosedImmersion j] in
/-- Ideal containment supplies all hypotheses for the canonical transition geometry. -/
theorem transition_geometry (h : D.I ≤ D'.I) :
    Smooth (transition c D D' h).hom.hom.hom.left ∧
      Surjective (transition c D D' h).hom.hom.hom.left ∧
      GeometricallyConnected (transition c D D' h).hom.hom.hom.left := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h) :=
    modulusIdealInclusion_isClosedImmersion c D D' h
  exact ⟨transitionAlong_smooth c D D' (Scheme.IdealSheafData.inclusion h)
      (modulusIdealInclusion_curve c D D' h),
    transitionAlong_surjective c D D' (Scheme.IdealSheafData.inclusion h)
      (modulusIdealInclusion_curve c D D' h),
    transitionAlong_geometricallyConnected c D D' (Scheme.IdealSheafData.inclusion h)
      (modulusIdealInclusion_curve c D D' h)⟩

end AlgebraicGeometry.GeneralizedJacobian
