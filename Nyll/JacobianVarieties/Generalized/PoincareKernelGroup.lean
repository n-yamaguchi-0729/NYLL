/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusNormBoundary
import Nyll.JacobianVarieties.Generalized.PoincareKernelScheme
import Nyll.JacobianVarieties.Generalized.PoincareProjectionSurjectivity
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIdentity
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # The actual identity fibre as the modulus-unit quotient group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open GoodReductionJacobian AlgebraicGeometry.RelPicard
open SchemeTheory.Affine AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J) (hd : 0 < d)

/-- The actual scalar boundary is represented by a homomorphism from the concrete norm open. -/
def poincareModulusUnitBoundary :
    modulusUnitQuotient D hd ⟶ poincareModulusCommGroupScheme D h hd :=
  SchemeTheory.RepresentedGroups.map _ _ (modulusUnitQuotientRepresentable D hd)
    (poincareModulusPicardZeroGroupRepresentable D h hd)
    (modulusNormBoundarySheaf D).hom

/-- Its composition with forgetting is the identity point, as an equality of scheme maps. -/
theorem poincareModulusUnitBoundary_condition :
    (poincareModulusUnitBoundary D h hd).hom.hom.hom ≫
      (poincareModulusGroupProjection D h hd).hom.hom.hom =
        (1 : (modulusUnitQuotient D hd).X ⟶ (ordinaryZeroCommGroupScheme h).X) := by
  let b := (poincareModulusUnitBoundary D h hd).hom.hom.hom
  let eU := modulusUnitQuotientRepresentable D hd
  let eM := poincareModulusPicardZeroGroupRepresentable D h hd
  let eJ := ordinaryZeroGroupSheafRepresentable h
  apply eJ.homEquiv.injective
  have hb := SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _ eU eM
    (modulusNormBoundarySheaf D).hom (𝟙 (modulusUnitQuotient D hd).X)
  rw [Category.id_comp] at hb
  change eM.homEquiv b = _ at hb
  have hr := (Set.ext_iff.mp (modulusNormBoundarySheaf_range D
    (modulusUnitQuotient D hd).X) _).mp ⟨eU.homEquiv (𝟙 _), rfl⟩
  exact (poincareModulusGroupProjection_homEquiv D h hd b).trans
    ((congrArg ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app
      (op (modulusUnitQuotient D hd).X)).hom hb).trans
        (hr.trans (SchemeTheory.RepresentedGroups.homEquiv_one _ eJ _).symm))

/-- The first projection from the genuine scheme-theoretic identity fibre. -/
def poincareModulusKernelInclusion :
    poincareModulusKernelScheme D h hd ⟶ (poincareModulusCommGroupScheme D h hd).X :=
  Over.homMk (pullback.fst (poincareModulusGroupProjection D h hd).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ordinaryZeroCommGroupScheme h).X).left)
      (by
        change pullback.fst _ _ ≫ (poincareModulusCommGroupScheme D h hd).X.hom = pullback.snd _ _
        rw [← Over.w (poincareModulusGroupProjection D h hd).hom.hom.hom,
          ← Category.assoc, pullback.condition, Category.assoc, Over.w]
        exact Category.comp_id _)

/-- The fibre inclusion lands at the actual identity point of the ordinary group. -/
theorem poincareModulusKernelInclusion_condition :
    poincareModulusKernelInclusion D h hd ≫
      (poincareModulusGroupProjection D h hd).hom.hom.hom =
        (1 : poincareModulusKernelScheme D h hd ⟶ (ordinaryZeroCommGroupScheme h).X) := by
  apply Over.OverMorphism.ext
  change pullback.fst _ _ ≫ _ = _
  rw [pullback.condition]
  simp only [CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

/-- The scalar boundary factors through that actual scheme fibre. -/
def poincareModulusUnitToKernel :
    (modulusUnitQuotient D hd).X ⟶ poincareModulusKernelScheme D h hd :=
  Over.homMk (pullback.lift
    (poincareModulusUnitBoundary D h hd).hom.hom.hom.left
    (modulusUnitQuotient D hd).X.hom (by
      have hb := congrArg Over.Hom.left (poincareModulusUnitBoundary_condition D h hd)
      let t : (modulusUnitQuotient D hd).X ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
        Over.homMk (modulusUnitQuotient D hd).X.hom (Category.comp_id _)
      exact hb.trans (congrArg Over.Hom.left
        (MonObj.comp_one (M := (ordinaryZeroCommGroupScheme h).X) t)).symm))
    (pullback.lift_snd _ _ _)

/-- The factorization retains the actual scalar boundary as its first projection. -/
@[reassoc] theorem poincareModulusUnitToKernel_inclusion :
    poincareModulusUnitToKernel D h hd ≫ poincareModulusKernelInclusion D h hd =
      (poincareModulusUnitBoundary D h hd).hom.hom.hom := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- Exactness on sheaf sections identifies this factorization with the entire identity fibre. -/
instance poincareModulusUnitToKernel_isIso : IsIso (poincareModulusUnitToKernel D h hd) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  let eU := modulusUnitQuotientRepresentable D hd
  let eM := poincareModulusPicardZeroGroupRepresentable D h hd
  let eJ := ordinaryZeroGroupSheafRepresentable h
  let b := (poincareModulusUnitBoundary D h hd).hom.hom.hom
  have hb (f : T ⟶ (modulusUnitQuotient D hd).X) :
      eM.homEquiv (f ≫ b) =
        ((modulusNormBoundarySheaf D).hom.app (op T)).hom (eU.homEquiv f) :=
    SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _ eU eM
      (modulusNormBoundarySheaf D).hom f
  constructor
  · intro f g hfg
    apply eU.homEquiv.injective
    apply (CommGrpCat.mono_iff_injective
      ((modulusNormBoundarySheaf D).hom.app (op T))).mp inferInstance
    rw [← hb, ← hb]
    apply congrArg eM.homEquiv
    have hp := congrArg (fun a => a ≫ poincareModulusKernelInclusion D h hd) hfg
    change f ≫ (poincareModulusUnitBoundary D h hd).hom.hom.hom =
      g ≫ (poincareModulusUnitBoundary D h hd).hom.hom.hom
    simpa only [Category.assoc, poincareModulusUnitToKernel_inclusion] using hp
  · intro r
    let x := eM.homEquiv (r ≫ poincareModulusKernelInclusion D h hd)
    have hx : ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom x =
        1 := by
      have hp : (r ≫ poincareModulusKernelInclusion D h hd) ≫
          (poincareModulusGroupProjection D h hd).hom.hom.hom = 1 := by
        rw [Category.assoc, poincareModulusKernelInclusion_condition, MonObj.comp_one]
      exact (poincareModulusGroupProjection_homEquiv D h hd
        (r ≫ poincareModulusKernelInclusion D h hd)).symm.trans
        ((congrArg eJ.homEquiv hp).trans
          (SchemeTheory.RepresentedGroups.homEquiv_one _ eJ T))
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (modulusNormBoundarySheaf_range D T) x).mpr hx
    refine ⟨eU.homEquiv.symm a, ?_⟩
    have hf : eU.homEquiv.symm a ≫ b = r ≫ poincareModulusKernelInclusion D h hd := by
      apply eM.homEquiv.injective
      exact (hb _).trans
        ((congrArg ((modulusNormBoundarySheaf D).hom.app (op T)).hom
          (eU.homEquiv.apply_symm_apply a)).trans ha)
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have hp : (eU.homEquiv.symm a ≫ poincareModulusUnitToKernel D h hd) ≫
          poincareModulusKernelInclusion D h hd = r ≫ poincareModulusKernelInclusion D h hd := by
        rw [Category.assoc, poincareModulusUnitToKernel_inclusion]
        exact hf
      exact congrArg Over.Hom.left hp
    · exact (Over.w (eU.homEquiv.symm a ≫ poincareModulusUnitToKernel D h hd)).trans
        (Over.w r).symm

/-- The identity fibre represents the same actual scalar group sheaf through the boundary. -/
def poincareModulusKernelGroupRepresentable :
    ((ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (poincareModulusKernelScheme D h hd) :=
  (modulusUnitQuotientRepresentable D hd).ofIsoObj
    (asIso (poincareModulusUnitToKernel D h hd)).symm

/-- The genuine identity fibre, with the group structure determined by the actual boundary. -/
def poincareModulusKernelCommGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject _ (poincareModulusKernelGroupRepresentable D h hd)

/-- The kernel is the concrete norm-open modulus-unit quotient as a commutative group scheme. -/
def poincareModulusKernelGroupIso :
    poincareModulusKernelCommGroupScheme D h hd ≅ modulusUnitQuotient D hd :=
  SchemeTheory.RepresentedGroups.iso _ _ (poincareModulusKernelGroupRepresentable D h hd)
    (modulusUnitQuotientRepresentable D hd) (Iso.refl _)

/-- The kernel group inclusion is the homomorphism induced by the actual scalar boundary. -/
def poincareModulusKernelGroupInclusion :
    poincareModulusKernelCommGroupScheme D h hd ⟶ poincareModulusCommGroupScheme D h hd :=
  SchemeTheory.RepresentedGroups.map _ _ (poincareModulusKernelGroupRepresentable D h hd)
    (poincareModulusPicardZeroGroupRepresentable D h hd)
    (modulusNormBoundarySheaf D).hom

/-- The represented group inclusion is exactly the projection from the scheme-theoretic fibre. -/
theorem poincareModulusKernelGroupInclusion_eq :
    (poincareModulusKernelGroupInclusion D h hd).hom.hom.hom =
      poincareModulusKernelInclusion D h hd := by
  let U := (modulusUnitQuotient D hd).X
  let Z := poincareModulusKernelScheme D h hd
  let eU := modulusUnitQuotientRepresentable D hd
  let eZ := poincareModulusKernelGroupRepresentable D h hd
  let eM := poincareModulusPicardZeroGroupRepresentable D h hd
  let e : U ≅ Z := asIso (poincareModulusUnitToKernel D h hd)
  apply eM.homEquiv.injective
  have hm := SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _ eZ eM
    (modulusNormBoundarySheaf D).hom (𝟙 Z)
  rw [Category.id_comp] at hm
  have hpoint : eZ.homEquiv (𝟙 Z) = eU.homEquiv e.inv := by
    change eU.homEquiv (𝟙 Z ≫ e.inv) = eU.homEquiv e.inv
    rw [Category.id_comp]
  have hb := SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _ eU eM
    (modulusNormBoundarySheaf D).hom e.inv
  have hf : e.inv ≫ (poincareModulusUnitBoundary D h hd).hom.hom.hom =
      poincareModulusKernelInclusion D h hd :=
    e.inv_comp_eq.mpr (poincareModulusUnitToKernel_inclusion D h hd).symm
  exact hm.trans
    ((congrArg ((modulusNormBoundarySheaf D).hom.app (op Z)).hom hpoint).trans
      (hb.symm.trans (congrArg eM.homEquiv hf)))

include h hd in
/-- The scalar quotient, modulus Picard-zero and ordinary Picard-zero form an exact fppf sequence:
the first map is injective, its image is the kernel, and the last map is locally surjective. -/
theorem poincareModulusGroupSheaf_exact :
    Mono (modulusNormBoundarySheaf D) ∧
      (∀ T : Over (Spec (CommRingCat.of K)),
        Set.range ((modulusNormBoundarySheaf D).hom.app (op T)).hom =
          {x | ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom x = 1}) ∧
      Sheaf.IsLocallySurjective (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) :=
  ⟨inferInstance, modulusNormBoundarySheaf_range D,
    forgetModulusZeroGroupSheaf_isLocallySurjective D h hd⟩

end AlgebraicGeometry.GeneralizedJacobian
