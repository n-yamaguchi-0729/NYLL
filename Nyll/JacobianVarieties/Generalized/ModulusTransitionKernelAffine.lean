/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusTransitionFibers
import Nyll.JacobianVarieties.Generalized.AbelianSchemeExamples
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affineness of the actual changing-modulus identity kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual identity fibre of forgetting the modulus is affine, including degree zero. -/
theorem groupKernelScheme_isAffine : IsAffine (groupKernelScheme c D).left := by
  cases d with
  | zero =>
      have : IsIso (groupProjection c D).hom.hom.hom.left :=
        inferInstanceAs (IsIso
          (((CommGrp.forget _ ⋙ Over.forget _).mapIso (emptyModulusGroupIso c D)).hom))
      change IsAffine (pullback (groupProjection c D).hom.hom.hom.left
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ordinaryGroupScheme c).X).left)
      exact IsAffine.of_isIso (h := inferInstanceAs (IsAffine (Spec (CommRingCat.of K))))
        (pullback.snd _ _)
  | succ n =>
      exact IsAffine.of_isIso
        (h := isAffine_modulusUnitQuotient D (Nat.zero_lt_succ n))
        (((Over.forget _).mapIso (asIso (modulusNormToKernel c D (Nat.zero_lt_succ n)))).inv)

/-- The ordinary identity fibre is a closed subscheme of the generalized Jacobian. -/
theorem groupKernelInclusion_isClosedImmersion :
    IsClosedImmersion (groupKernelInclusion c D).left := by
  let z : Spec (CommRingCat.of K) ⟶ (ordinaryGroupScheme c).X.left :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ordinaryGroupScheme c).X).left
  have : IsClosedImmersion (z ≫ (ordinaryGroupScheme c).X.hom) := by
    change IsClosedImmersion ((1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (ordinaryGroupScheme c).X).left ≫ (ordinaryGroupScheme c).X.hom)
    rw [Over.w]
    exact inferInstanceAs (IsClosedImmersion (𝟙 (Spec (CommRingCat.of K))))
  have : IsClosedImmersion z := IsClosedImmersion.of_comp z (ordinaryGroupScheme c).X.hom
  change IsClosedImmersion (pullback.fst (groupProjection c D).hom.hom.hom.left z)
  infer_instance

variable (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)

/-- The inclusion of the literal scheme-theoretic identity fibre of restriction. -/
def transitionKernelInclusion : transitionKernelScheme c D D' j w ⟶ (groupScheme c D).X :=
  Over.homMk (pullback.fst (transitionAlong c D D' j w).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme c D').X).left) (by
      change pullback.fst _ _ ≫ (groupScheme c D).X.hom = pullback.snd _ _
      rw [← Over.w (transitionAlong c D D' j w).hom.hom.hom,
        ← Category.assoc, pullback.condition, Category.assoc, Over.w]
      exact Category.comp_id _)

/-- The actual fibre inclusion maps to the identity under restriction. -/
theorem transitionKernelInclusion_condition :
    transitionKernelInclusion c D D' j w ≫ (transitionAlong c D D' j w).hom.hom.hom = 1 := by
  apply Over.OverMorphism.ext
  change pullback.fst _ _ ≫ _ = _
  rw [pullback.condition]
  simp only [CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

/-- In particular, forgetting the modulus kills the whole actual transition kernel. -/
theorem transitionKernelInclusion_projection :
    transitionKernelInclusion c D D' j w ≫ (groupProjection c D).hom.hom.hom = 1 := by
  rw [← transitionAlong_groupProjection c D D' j w, ← Category.assoc,
    transitionKernelInclusion_condition, MonObj.one_comp]

/-- The transition identity fibre is a closed subscheme because the target group is separated. -/
theorem transitionKernelInclusion_isClosedImmersion :
    IsClosedImmersion (transitionKernelInclusion c D D' j w).left := by
  have : IsSeparated (groupScheme c D').X.hom := (geometry c D').2.2.2.1
  let z : Spec (CommRingCat.of K) ⟶ (groupScheme c D').X.left :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme c D').X).left
  have : IsClosedImmersion (z ≫ (groupScheme c D').X.hom) := by
    change IsClosedImmersion ((1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (groupScheme c D').X).left ≫ (groupScheme c D').X.hom)
    rw [Over.w]
    exact inferInstanceAs (IsClosedImmersion (𝟙 (Spec (CommRingCat.of K))))
  have : IsClosedImmersion z := IsClosedImmersion.of_comp z (groupScheme c D').X.hom
  change IsClosedImmersion (pullback.fst (transitionAlong c D D' j w).hom.hom.hom.left z)
  infer_instance

/-- The whole transition kernel maps canonically into the actual affine ordinary kernel. -/
def transitionKernelToOrdinaryKernel :
    transitionKernelScheme c D D' j w ⟶ groupKernelScheme c D :=
  Over.homMk (pullback.lift (transitionKernelInclusion c D D' j w).left
    (transitionKernelScheme c D D' j w).hom (by
      have hb := congrArg Over.Hom.left (transitionKernelInclusion_projection c D D' j w)
      let t : transitionKernelScheme c D D' j w ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
        Over.homMk (transitionKernelScheme c D D' j w).hom (Category.comp_id _)
      exact hb.trans (congrArg Over.Hom.left
        (MonObj.comp_one (M := (ordinaryGroupScheme c).X) t)).symm))
    (pullback.lift_snd _ _ _)

/-- The factorization preserves the original inclusion into the generalized Jacobian. -/
@[reassoc] theorem transitionKernelToOrdinaryKernel_inclusion :
    transitionKernelToOrdinaryKernel c D D' j w ≫ groupKernelInclusion c D =
      transitionKernelInclusion c D D' j w := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- This actual factorization is a closed immersion into the affine ordinary kernel. -/
theorem transitionKernelToOrdinaryKernel_isClosedImmersion :
    IsClosedImmersion (transitionKernelToOrdinaryKernel c D D' j w).left := by
  have : IsClosedImmersion (groupKernelInclusion c D).left :=
    groupKernelInclusion_isClosedImmersion c D
  have : IsClosedImmersion ((transitionKernelToOrdinaryKernel c D D' j w).left ≫
      (groupKernelInclusion c D).left) := by
    rw [← Over.comp_left, transitionKernelToOrdinaryKernel_inclusion]
    exact transitionKernelInclusion_isClosedImmersion c D D' j w
  exact IsClosedImmersion.of_comp (transitionKernelToOrdinaryKernel c D D' j w).left
    (groupKernelInclusion c D).left

/-- The literal scheme-theoretic transition kernel is affine over the original field. -/
theorem transitionKernelScheme_isAffine : IsAffine (transitionKernelScheme c D D' j w).left := by
  have : IsAffine (groupKernelScheme c D).left := groupKernelScheme_isAffine c D
  have : IsClosedImmersion (transitionKernelToOrdinaryKernel c D D' j w).left :=
    transitionKernelToOrdinaryKernel_isClosedImmersion c D D' j w
  exact isAffine_of_isAffineHom (transitionKernelToOrdinaryKernel c D D' j w).left

variable [IsClosedImmersion j]

/-- Every geometric fibre of actual restriction is integral. -/
theorem transitionAlong_geometricallyIntegral :
    GeometricallyIntegral (transitionAlong c D D' j w).hom.hom.hom.left := by
  have : Smooth (transitionAlong c D D' j w).hom.hom.hom.left :=
    transitionAlong_smooth c D D' j w
  have : GeometricallyConnected (transitionAlong c D D' j w).hom.hom.hom.left :=
    transitionAlong_geometricallyConnected c D D' j w
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected _

/-- The actual affine transition kernel remains integral after every field extension. -/
theorem transitionKernelScheme_geometricallyIntegral :
    GeometricallyIntegral (transitionKernelScheme c D D' j w).hom := by
  have : Smooth (transitionKernelScheme c D D' j w).hom :=
    transitionKernelScheme_smooth c D D' j w
  have : GeometricallyConnected (transitionKernelScheme c D D' j w).hom :=
    transitionKernelScheme_geometricallyConnected c D D' j w
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected _

end AlgebraicGeometry.GeneralizedJacobian
