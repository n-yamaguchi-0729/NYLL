/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.ModulusTransition
import Nyll.JacobianVarieties.Generalized.ModulusRestrictionForgetful
import Nyll.JacobianVarieties.Generalized.ModulusNormKernel
import Nyll.SchemeTheory.GroupSchemes.KernelTranslation

/-! # The actual translation square for changing-modulus transitions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- The actual norm boundary distinguishes all morphisms from any parameter scheme. -/
theorem modulusNormBoundary_postcomp_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (fun a : T ⟶ (modulusUnitQuotient D hd).X =>
      a ≫ (modulusNormBoundary c D hd).hom.hom.hom) := by
  intro a b hab
  apply (modulusUnitQuotientRepresentable D hd).homEquiv.injective
  apply (CommGrpCat.mono_iff_injective
    ((modulusNormBoundarySheaf D).hom.app (op T))).mp inferInstance
  rw [← modulusNormBoundary_homEquiv c D hd, ← modulusNormBoundary_homEquiv c D hd]
  exact congrArg (groupRepresentable c D).homEquiv hab

/-- The proved sheaf kernel identifies exactly the morphisms landing in the identity fibre. -/
theorem exists_modulusNormBoundary_eq_iff {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (groupScheme c D).X) :
    (∃ a : T ⟶ (modulusUnitQuotient D hd).X,
      a ≫ (modulusNormBoundary c D hd).hom.hom.hom = x) ↔
        x ≫ (groupProjection c D).hom.hom.hom = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [Category.assoc, modulusNormBoundary_condition, MonObj.comp_one]
  · intro hx
    have hclass : ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom
        ((groupRepresentable c D).homEquiv x) = 1 := by
      exact (groupProjection_homEquiv c D x).symm.trans
        ((congrArg (ordinaryGroupRepresentable c).homEquiv hx).trans
          (SchemeTheory.RepresentedGroups.homEquiv_one _ (ordinaryGroupRepresentable c) T))
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (modulusNormBoundarySheaf_range D T) _).mpr hclass
    refine ⟨(modulusUnitQuotientRepresentable D hd).homEquiv.symm a, ?_⟩
    apply (groupRepresentable c D).homEquiv.injective
    rw [modulusNormBoundary_homEquiv, Equiv.apply_symm_apply]
    exact ha

end AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)

/-- The canonical transition is a morphism over the actual ordinary Jacobian. -/
@[reassoc] theorem transitionAlong_groupProjection :
    (transitionAlong c D D' j w).hom.hom.hom ≫ (groupProjection c D').hom.hom.hom =
      (groupProjection c D).hom.hom.hom := by
  let T := (groupScheme c D).X
  let x := (groupRepresentable c D).homEquiv (𝟙 T)
  apply (ordinaryGroupRepresentable c).homEquiv.injective
  have ht := transitionAlong_homEquiv c D D' j w (𝟙 T)
  rw [Category.id_comp] at ht
  have hp := groupProjection_homEquiv c D (𝟙 T)
  change (ordinaryGroupRepresentable c).homEquiv (groupProjection c D).hom.hom.hom = _ at hp
  have hs := congrArg
    (fun f : modulusPicardZeroGroupSheaf c (modulusCurveMap D) ⟶
        ordinaryRelativePicardZeroGroupSheaf c => (f.hom.app (op T)).hom x)
      (modulusRestrictionZeroSheaf_forget c j w)
  exact (groupProjection_homEquiv c D' (transitionAlong c D D' j w).hom.hom.hom).trans
    ((congrArg ((forgetModulusZeroGroupSheaf c (modulusCurveMap D')).hom.app (op T)).hom ht).trans
      (hs.trans hp.symm))

variable (hd' : 0 < d')

/-- Translate the canonical restriction of a point by the actual smaller-modulus boundary. -/
def transitionUnitAction :
    Limits.prod (groupScheme c D).X (modulusUnitQuotient D' hd').X ⟶ (groupScheme c D').X :=
  (Limits.prod.fst (X := (groupScheme c D).X) (Y := (modulusUnitQuotient D' hd').X) ≫
    (transitionAlong c D D' j w).hom.hom.hom) *
    (Limits.prod.snd (X := (groupScheme c D).X) (Y := (modulusUnitQuotient D' hd').X) ≫
      (modulusNormBoundary c D' hd').hom.hom.hom)

/-- Translation by a scalar boundary fixes the actual ordinary Picard class. -/
@[reassoc] theorem transitionUnitAction_projection :
    transitionUnitAction c D D' j w hd' ≫ (groupProjection c D').hom.hom.hom =
      Limits.prod.fst ≫ (groupProjection c D).hom.hom.hom := by
  simp only [transitionUnitAction, MonObj.mul_comp, Category.assoc,
    transitionAlong_groupProjection, modulusNormBoundary_condition, MonObj.comp_one, mul_one]

/-- The norm-boundary translation square is an actual pullback of schemes over the field.
The lifting and uniqueness are proved from the boundary kernel, without a torsor hypothesis. -/
theorem transitionUnitAction_isPullback :
    IsPullback (transitionUnitAction c D D' j w hd') Limits.prod.fst
      (groupProjection c D').hom.hom.hom (groupProjection c D).hom.hom.hom := by
  have h := GroupSchemes.kernelTranslation_isPullback
    (transitionAlong c D D' j w) (modulusNormBoundary c D' hd')
    (groupProjection c D') (modulusNormBoundary_condition c D' hd')
    (modulusNormBoundaryIsKernel c D' hd')
  simpa only [transitionUnitAction, GroupSchemes.kernelTranslation,
    transitionAlong_groupProjection] using h

/-- The canonical translation trivialization after pullback along the source projection. -/
def transitionUnitActionIso :
    Limits.prod (groupScheme c D).X (modulusUnitQuotient D' hd').X ≅
      pullback (groupProjection c D).hom.hom.hom (groupProjection c D').hom.hom.hom :=
  (transitionUnitAction_isPullback c D D' j w hd').flip.isoPullback

/-- The first component of the trivialization is the original source point. -/
@[reassoc] theorem transitionUnitActionIso_fst :
    (transitionUnitActionIso c D D' j w hd').hom ≫ pullback.fst _ _ = Limits.prod.fst :=
  (transitionUnitAction_isPullback c D D' j w hd').flip.isoPullback_hom_fst

/-- The second component is restriction followed by the actual norm-boundary translation. -/
@[reassoc] theorem transitionUnitActionIso_snd :
    (transitionUnitActionIso c D D' j w hd').hom ≫ pullback.snd _ _ =
      transitionUnitAction c D D' j w hd' :=
  (transitionUnitAction_isPullback c D D' j w hd').flip.isoPullback_hom_snd

end AlgebraicGeometry.GeneralizedJacobian
