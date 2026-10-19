/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusNormRestriction
import Nyll.JacobianVarieties.Generalized.ModulusTransitionTorsor
import Nyll.JacobianVarieties.Generalized.GroupProjectionGeometry
import Nyll.JacobianVarieties.Generalized.GroupProjectionSurjective
import Nyll.SchemeTheory.Morphisms.GeometricallyConnectedDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Geometry of the actual changing-modulus transition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
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
  (hd : 0 < d) (hd' : 0 < d')

/-- Restrict only the norm coordinate in the actual translation trivializations. -/
def transitionNormProductMap :
    Limits.prod (groupScheme c D).X (modulusUnitQuotient D hd).X ⟶
      Limits.prod (groupScheme c D).X (modulusUnitQuotient D' hd').X :=
  Limits.prod.map (𝟙 (groupScheme c D).X) (modulusNormRestriction D D' j w hd hd')

/-- The coordinate restriction commutes with the actual translation actions. -/
theorem transitionNormProductMap_action :
    transitionNormProductMap c D D' j w hd hd' ≫ transitionUnitAction c D D' j w hd' =
      transitionUnitAction c D D (𝟙 _) (Category.id_comp (modulusCurveMap D)).symm hd ≫
        (transitionAlong c D D' j w).hom.hom.hom := by
  have hid : (transitionAlong c D D (𝟙 _)
      (Category.id_comp (modulusCurveMap D)).symm).hom.hom.hom = 𝟙 (groupScheme c D).X := by
    rw [transitionAlong_id]
    rfl
  simp only [transitionNormProductMap, transitionUnitAction, MonObj.comp_mul,
    MonObj.mul_comp, Category.assoc, Limits.prod.map_fst_assoc, Limits.prod.map_snd_assoc,
    Category.id_comp, hid,
    Category.comp_id, modulusNormBoundary_restriction]

/-- The actual transition becomes restriction on the norm coordinate after pullback
along the canonical translation cover. -/
theorem transitionNormProductMap_isPullback :
    IsPullback (transitionNormProductMap c D D' j w hd hd')
      (transitionUnitAction c D D (𝟙 _) (Category.id_comp (modulusCurveMap D)).symm hd)
      (transitionUnitAction c D D' j w hd') (transitionAlong c D D' j w).hom.hom.hom := by
  apply IsPullback.of_right (h₁₂ := Limits.prod.fst)
    (h₂₂ := (groupProjection c D').hom.hom.hom) ?_
    (transitionNormProductMap_action c D D' j w hd hd')
    (transitionUnitAction_isPullback c D D' j w hd').flip
  rw [transitionNormProductMap, Limits.prod.map_fst, Category.comp_id,
    transitionAlong_groupProjection]
  exact (transitionUnitAction_isPullback c D D (𝟙 _)
    (Category.id_comp (modulusCurveMap D)).symm hd).flip

/-- Restricting the norm coordinate is a literal base change of actual norm restriction. -/
theorem transitionNormProductMap_norm_isPullback :
    IsPullback Limits.prod.snd (transitionNormProductMap c D D' j w hd hd')
      (modulusNormRestriction D D' j w hd hd') Limits.prod.snd := by
  apply (IsPullback.of_prod_fst_with_id (modulusNormRestriction D D' j w hd hd')
    (groupScheme c D).X).of_iso'
    (Limits.prod.braiding (groupScheme c D).X (modulusUnitQuotient D hd).X)
    (Iso.refl _) (Limits.prod.braiding (groupScheme c D).X
      (modulusUnitQuotient D' hd').X) (Iso.refl _)
  · simp only [Limits.prod.braiding_hom, Limits.prod.lift_fst, Iso.refl_hom, Category.comp_id]
  · exact (Limits.braid_natural (𝟙 (groupScheme c D).X)
      (modulusNormRestriction D D' j w hd hd')).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Limits.prod.braiding_hom, Limits.prod.lift_fst, Iso.refl_hom, Category.comp_id]

/-- The translation cover is smooth because it is the base change of the proved
ordinary-Jacobian projection. -/
theorem transitionUnitAction_smooth : Smooth (transitionUnitAction c D D' j w hd').left :=
  smooth_isStableUnderBaseChange.of_isPullback
    ((transitionUnitAction_isPullback c D D' j w hd').flip.map (Over.forget _))
    (groupProjection_smooth c D)

/-- The same actual translation cover is surjective. -/
theorem transitionUnitAction_surjective :
    Surjective (transitionUnitAction c D D' j w hd').left :=
  MorphismProperty.of_isPullback
    ((transitionUnitAction_isPullback c D D' j w hd').flip.map (Over.forget _))
    (groupProjection_surjective c D)

private theorem groupProjection_quasiCompact :
    QuasiCompact (groupProjection c D).hom.hom.hom.left := by
  have : IsProper (ordinaryGroupScheme c).X.hom :=
    (Unpointed.zeroDegreeGeometry c (RelEffCartierDiv.empty c (𝟙 _))).2.1
  have : QuasiCompact ((groupProjection c D).hom.hom.hom.left ≫
      (ordinaryGroupScheme c).X.hom) := by
    rw [Over.w]
    exact (geometry c D).2.2.1
  exact QuasiCompact.of_comp (groupProjection c D).hom.hom.hom.left (ordinaryGroupScheme c).X.hom

variable [IsClosedImmersion j]

include hd hd' in
/-- Changing to a smaller positive modulus is smooth on the actual generalized Jacobians. -/
theorem transitionAlong_smooth_of_pos : Smooth (transitionAlong c D D' j w).hom.hom.hom.left := by
  have hsm : Smooth (transitionNormProductMap c D D' j w hd hd').left :=
    smooth_isStableUnderBaseChange.of_isPullback
      ((transitionNormProductMap_norm_isPullback c D D' j w hd hd').map (Over.forget _))
      (modulusNormRestriction_smooth D D' j w hd hd')
  have : Smooth (transitionUnitAction c D D' j w hd').left :=
    transitionUnitAction_smooth c D D' j w hd'
  have : Surjective (transitionUnitAction c D D' j w hd').left :=
    transitionUnitAction_surjective c D D' j w hd'
  have : QuasiCompact (transitionUnitAction c D D' j w hd').left :=
    MorphismProperty.of_isPullback
      ((transitionUnitAction_isPullback c D D' j w hd').flip.map (Over.forget _))
      (groupProjection_quasiCompact c D)
  have : MorphismProperty.DescendsAlong (@Smooth : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((transitionNormProductMap_isPullback c D D' j w hd hd').map (Over.forget _))
    ⟨⟨inferInstanceAs (Surjective (transitionUnitAction c D D' j w hd').left),
      inferInstanceAs (Flat (transitionUnitAction c D D' j w hd').left)⟩,
      inferInstanceAs (QuasiCompact (transitionUnitAction c D D' j w hd').left)⟩ hsm

include hd hd' in
/-- The canonical transition to a smaller positive modulus is surjective. -/
theorem transitionAlong_surjective_of_pos :
    Surjective (transitionAlong c D D' j w).hom.hom.hom.left := by
  have : Surjective (transitionNormProductMap c D D' j w hd hd').left :=
    MorphismProperty.of_isPullback
      ((transitionNormProductMap_norm_isPullback c D D' j w hd hd').map (Over.forget _))
      (modulusNormRestriction_surjective D D' j w hd hd')
  have : Surjective (transitionUnitAction c D D' j w hd').left :=
    transitionUnitAction_surjective c D D' j w hd'
  have hs : Surjective ((transitionNormProductMap c D D' j w hd hd').left ≫
      (transitionUnitAction c D D' j w hd').left) := inferInstance
  rw [← Over.comp_left, transitionNormProductMap_action, Over.comp_left] at hs
  exact Surjective.of_comp
    (transitionUnitAction c D D (𝟙 _) (Category.id_comp (modulusCurveMap D)).symm hd).left
    (transitionAlong c D D' j w).hom.hom.hom.left

include hd hd' in
/-- Every geometric fibre of the canonical transition to a smaller positive modulus
is connected, by actual norm restriction and surjective descent. -/
theorem transitionAlong_geometricallyConnected_of_pos :
    GeometricallyConnected (transitionAlong c D D' j w).hom.hom.hom.left := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    GeometricallyConnected.eq_geometrically ▸ inferInstance
  have hg : GeometricallyConnected (transitionNormProductMap c D D' j w hd hd').left :=
    hbc.of_isPullback
      ((transitionNormProductMap_norm_isPullback c D D' j w hd hd').map (Over.forget _))
      (modulusNormRestriction_geometricallyConnected D D' j w hd hd')
  exact MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective)
    ((transitionNormProductMap_isPullback c D D' j w hd hd').map (Over.forget _))
    (transitionUnitAction_surjective c D D' j w hd') hg

end AlgebraicGeometry.GeneralizedJacobian
