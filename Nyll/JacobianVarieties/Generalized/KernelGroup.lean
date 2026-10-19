/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusNormBoundary
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivSum
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIdentity
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # The norm-open kernel group of the generalized Jacobian over an arbitrary field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard
open SchemeTheory.Affine AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The ordinary Picard-zero representation supplied by the constructed empty-modulus scheme. -/
def ordinaryGroupRepresentable :
    ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙ forget CommGrpCat.{u + 1}).RepresentableBy
      (Unpointed.zeroDegreeGroupScheme c (RelEffCartierDiv.empty c (𝟙 _))).X :=
  Unpointed.zeroDegreeOrdinaryGroupRepresentable c (RelEffCartierDiv.empty c (𝟙 _))

/-- The ordinary Jacobian group from its proved unpointed representation. -/
def ordinaryGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject _ (ordinaryGroupRepresentable c)

variable {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- Forgetting the modulus is a homomorphism of the groups constructed over the original field. -/
def groupProjection : groupScheme c D ⟶ ordinaryGroupScheme c := by
  cases d <;>
    exact SchemeTheory.RepresentedGroups.map _ _ (groupRepresentable c D)
      (ordinaryGroupRepresentable c) (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom

/-- The underlying projection is the map supplied by the actual representing equivalences. -/
theorem groupProjection_hom :
    (groupProjection c D).hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism _ _ (groupRepresentable c D)
        (ordinaryGroupRepresentable c)
        (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom := by
  cases d <;> rfl

/-- On every parameter scheme this morphism is the actual forgetting of rigidification. -/
theorem groupProjection_homEquiv {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (groupScheme c D).X) :
    (ordinaryGroupRepresentable c).homEquiv (f ≫ (groupProjection c D).hom.hom.hom) =
      ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom
        ((groupRepresentable c D).homEquiv f) := by
  exact (congrArg (fun m : (groupScheme c D).X ⟶ (ordinaryGroupScheme c).X =>
    (ordinaryGroupRepresentable c).homEquiv (f ≫ m)) (groupProjection_hom c D)).trans
      (SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _
        (groupRepresentable c D) (ordinaryGroupRepresentable c)
        (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom f)

/-- In degree zero the actual forgetful group morphism is the ordinary Jacobian isomorphism. -/
def emptyModulusGroupIso
    (D₀ : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K)))) :
    groupScheme c D₀ ≅ ordinaryGroupScheme c :=
  SchemeTheory.RepresentedGroups.iso _ _ (groupRepresentable c D₀)
    (ordinaryGroupRepresentable c)
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      CommGrpCat.{u + 1}).mapIso (Pointed.zeroDegreeSheafIso c D₀))

/-- The empty-modulus isomorphism is the actual forgetting homomorphism. -/
theorem emptyModulusGroupIso_hom
    (D₀ : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K)))) :
    (emptyModulusGroupIso c D₀).hom = groupProjection c D₀ := rfl

/-- The actual scheme-theoretic identity fibre of the arbitrary-field projection. -/
def groupKernelScheme : Over (Spec (CommRingCat.of K)) :=
  Over.mk (pullback.snd (groupProjection c D).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ordinaryGroupScheme c).X).left)

variable (hd : 0 < d)

/-- The actual scalar boundary is represented by a homomorphism from the concrete norm open. -/
def modulusNormBoundary :
    modulusUnitQuotient D hd ⟶ groupScheme c D := by
  cases d with
  | zero => omega
  | succ n =>
      exact SchemeTheory.RepresentedGroups.map _ _ (modulusUnitQuotientRepresentable D hd)
        (groupRepresentable c D)
        (modulusNormBoundarySheaf D).hom

/-- The underlying scalar boundary is the map supplied by the representing equivalences. -/
theorem modulusNormBoundary_hom :
    (modulusNormBoundary c D hd).hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism _ _ (modulusUnitQuotientRepresentable D hd)
        (groupRepresentable c D) (modulusNormBoundarySheaf D).hom := by
  cases d with
  | zero => omega
  | succ n => rfl

/-- The scalar boundary classifies the actual boundary of every norm-open point. -/
theorem modulusNormBoundary_homEquiv {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (modulusUnitQuotient D hd).X) :
    (groupRepresentable c D).homEquiv (f ≫ (modulusNormBoundary c D hd).hom.hom.hom) =
      ((modulusNormBoundarySheaf D).hom.app (op T)).hom
        ((modulusUnitQuotientRepresentable D hd).homEquiv f) :=
  (congrArg (fun m : (modulusUnitQuotient D hd).X ⟶ (groupScheme c D).X =>
    (groupRepresentable c D).homEquiv (f ≫ m)) (modulusNormBoundary_hom c D hd)).trans
      (SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _
        (modulusUnitQuotientRepresentable D hd) (groupRepresentable c D)
        (modulusNormBoundarySheaf D).hom f)

/-- Its composition with forgetting is the identity point, as an equality of scheme maps. -/
theorem modulusNormBoundary_condition :
    (modulusNormBoundary c D hd).hom.hom.hom ≫
      (groupProjection c D).hom.hom.hom =
        (1 : (modulusUnitQuotient D hd).X ⟶ (ordinaryGroupScheme c).X) := by
  let b := (modulusNormBoundary c D hd).hom.hom.hom
  let eU := modulusUnitQuotientRepresentable D hd
  let eM := groupRepresentable c D
  let eJ := ordinaryGroupRepresentable c
  apply eJ.homEquiv.injective
  have hb := modulusNormBoundary_homEquiv c D hd (𝟙 (modulusUnitQuotient D hd).X)
  rw [Category.id_comp] at hb
  change eM.homEquiv b = _ at hb
  have hr := (Set.ext_iff.mp (modulusNormBoundarySheaf_range D
    (modulusUnitQuotient D hd).X) _).mp ⟨eU.homEquiv (𝟙 _), rfl⟩
  exact (groupProjection_homEquiv c D b).trans
    ((congrArg ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app
      (op (modulusUnitQuotient D hd).X)).hom hb).trans
        (hr.trans (SchemeTheory.RepresentedGroups.homEquiv_one _ eJ _).symm))

omit hd in
/-- The first projection from the genuine scheme-theoretic identity fibre. -/
def groupKernelInclusion :
    groupKernelScheme c D ⟶ (groupScheme c D).X :=
  Over.homMk (pullback.fst (groupProjection c D).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ordinaryGroupScheme c).X).left)
      (by
        change pullback.fst _ _ ≫ (groupScheme c D).X.hom = pullback.snd _ _
        rw [← Over.w (groupProjection c D).hom.hom.hom,
          ← Category.assoc, pullback.condition, Category.assoc, Over.w]
        exact Category.comp_id _)

omit hd in
/-- The fibre inclusion lands at the actual identity point of the ordinary group. -/
theorem groupKernelInclusion_condition :
    groupKernelInclusion c D ≫
      (groupProjection c D).hom.hom.hom =
        (1 : groupKernelScheme c D ⟶ (ordinaryGroupScheme c).X) := by
  apply Over.OverMorphism.ext
  change pullback.fst _ _ ≫ _ = _
  rw [pullback.condition]
  simp only [CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

/-- The scalar boundary factors through that actual scheme fibre. -/
def modulusNormToKernel :
    (modulusUnitQuotient D hd).X ⟶ groupKernelScheme c D :=
  Over.homMk (pullback.lift
    (modulusNormBoundary c D hd).hom.hom.hom.left
    (modulusUnitQuotient D hd).X.hom (by
      have hb := congrArg Over.Hom.left (modulusNormBoundary_condition c D hd)
      let t : (modulusUnitQuotient D hd).X ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
        Over.homMk (modulusUnitQuotient D hd).X.hom (Category.comp_id _)
      exact hb.trans (congrArg Over.Hom.left
        (MonObj.comp_one (M := (ordinaryGroupScheme c).X) t)).symm))
    (pullback.lift_snd _ _ _)

/-- The factorization retains the actual scalar boundary as its first projection. -/
@[reassoc] theorem modulusNormToKernel_inclusion :
    modulusNormToKernel c D hd ≫ groupKernelInclusion c D =
      (modulusNormBoundary c D hd).hom.hom.hom := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- Exactness on sheaf sections identifies this factorization with the entire identity fibre. -/
instance modulusNormToKernel_isIso : IsIso (modulusNormToKernel c D hd) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  let eU := modulusUnitQuotientRepresentable D hd
  let eM := groupRepresentable c D
  let eJ := ordinaryGroupRepresentable c
  let b := (modulusNormBoundary c D hd).hom.hom.hom
  have hb (f : T ⟶ (modulusUnitQuotient D hd).X) :
      eM.homEquiv (f ≫ b) =
        ((modulusNormBoundarySheaf D).hom.app (op T)).hom (eU.homEquiv f) :=
    modulusNormBoundary_homEquiv c D hd f
  constructor
  · intro f g hfg
    apply eU.homEquiv.injective
    apply (CommGrpCat.mono_iff_injective
      ((modulusNormBoundarySheaf D).hom.app (op T))).mp inferInstance
    rw [← hb, ← hb]
    apply congrArg eM.homEquiv
    have hp := congrArg (fun a => a ≫ groupKernelInclusion c D) hfg
    change f ≫ (modulusNormBoundary c D hd).hom.hom.hom =
      g ≫ (modulusNormBoundary c D hd).hom.hom.hom
    simpa only [Category.assoc, modulusNormToKernel_inclusion] using hp
  · intro r
    let x := eM.homEquiv (r ≫ groupKernelInclusion c D)
    have hx : ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom x =
        1 := by
      have hp : (r ≫ groupKernelInclusion c D) ≫
          (groupProjection c D).hom.hom.hom = 1 := by
        rw [Category.assoc, groupKernelInclusion_condition, MonObj.comp_one]
      exact (groupProjection_homEquiv c D (r ≫ groupKernelInclusion c D)).symm.trans
        ((congrArg eJ.homEquiv hp).trans
          (SchemeTheory.RepresentedGroups.homEquiv_one _ eJ T))
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (modulusNormBoundarySheaf_range D T) x).mpr hx
    refine ⟨eU.homEquiv.symm a, ?_⟩
    have hf : eU.homEquiv.symm a ≫ b = r ≫ groupKernelInclusion c D := by
      apply eM.homEquiv.injective
      exact (hb _).trans
        ((congrArg ((modulusNormBoundarySheaf D).hom.app (op T)).hom
          (eU.homEquiv.apply_symm_apply a)).trans ha)
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have hp : (eU.homEquiv.symm a ≫ modulusNormToKernel c D hd) ≫
          groupKernelInclusion c D = r ≫ groupKernelInclusion c D := by
        rw [Category.assoc, modulusNormToKernel_inclusion]
        exact hf
      exact congrArg Over.Hom.left hp
    · exact (Over.w (eU.homEquiv.symm a ≫ modulusNormToKernel c D hd)).trans
        (Over.w r).symm

/-- The identity fibre represents the same actual scalar group sheaf through the boundary. -/
def kernelGroupRepresentable :
    ((ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (groupKernelScheme c D) :=
  (modulusUnitQuotientRepresentable D hd).ofIsoObj
    (asIso (modulusNormToKernel c D hd)).symm

/-- The genuine identity fibre, with the group structure determined by the actual boundary. -/
def kernelGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject _ (kernelGroupRepresentable c D hd)

/-- The kernel is the concrete norm-open modulus-unit quotient as a commutative group scheme. -/
def kernelGroupIso :
    kernelGroupScheme c D hd ≅ modulusUnitQuotient D hd :=
  SchemeTheory.RepresentedGroups.iso _ _ (kernelGroupRepresentable c D hd)
    (modulusUnitQuotientRepresentable D hd) (Iso.refl _)

/-- The kernel group inclusion is the homomorphism induced by the actual scalar boundary. -/
def kernelGroupInclusion :
    kernelGroupScheme c D hd ⟶ groupScheme c D := by
  cases d with
  | zero => omega
  | succ n =>
      exact SchemeTheory.RepresentedGroups.map _ _ (kernelGroupRepresentable c D hd)
        (groupRepresentable c D)
        (modulusNormBoundarySheaf D).hom

/-- The underlying kernel homomorphism is supplied by the representing equivalences. -/
theorem kernelGroupInclusion_hom :
    (kernelGroupInclusion c D hd).hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism _ _ (kernelGroupRepresentable c D hd)
        (groupRepresentable c D) (modulusNormBoundarySheaf D).hom := by
  cases d with
  | zero => omega
  | succ n => rfl

/-- The represented group inclusion is exactly the projection from the scheme-theoretic fibre. -/
theorem kernelGroupInclusion_eq :
    (kernelGroupInclusion c D hd).hom.hom.hom =
      groupKernelInclusion c D := by
  let U := (modulusUnitQuotient D hd).X
  let Z := groupKernelScheme c D
  let eU := modulusUnitQuotientRepresentable D hd
  let eZ := kernelGroupRepresentable c D hd
  let eM := groupRepresentable c D
  let e : U ≅ Z := asIso (modulusNormToKernel c D hd)
  apply eM.homEquiv.injective
  have hm := SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _ eZ eM
    (modulusNormBoundarySheaf D).hom (𝟙 Z)
  rw [Category.id_comp] at hm
  have hpoint : eZ.homEquiv (𝟙 Z) = eU.homEquiv e.inv := by
    change eU.homEquiv (𝟙 Z ≫ e.inv) = eU.homEquiv e.inv
    rw [Category.id_comp]
  have hb := modulusNormBoundary_homEquiv c D hd e.inv
  have hf : e.inv ≫ (modulusNormBoundary c D hd).hom.hom.hom =
      groupKernelInclusion c D :=
    e.inv_comp_eq.mpr (modulusNormToKernel_inclusion c D hd).symm
  exact (congrArg eM.homEquiv (kernelGroupInclusion_hom c D hd)).trans
    (hm.trans
      ((congrArg ((modulusNormBoundarySheaf D).hom.app (op Z)).hom hpoint).trans
        (hb.symm.trans (congrArg eM.homEquiv hf))))



end AlgebraicGeometry.GeneralizedJacobian
