/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ExistingJacobianSheafRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.GroupOfMatching
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# The actual ordinary sheaf represents the existing unpointed group law

The descended universal class restricts to the sheafification of the original
raw local class. Tensor products are therefore compatible with the already
constructed relative group law, using separatedness of the actual fppf sheaf.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.GeneralizedJacobian NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}

local instance presentationExtensionField (M : Presentation K c) : Field M.extension :=
  M.extensionField
local instance presentationExtensionAlgebra (M : Presentation K c) : Algebra K M.extension :=
  M.extensionAlgebra
local instance presentationExtensionFinite (M : Presentation K c) : Module.Finite K M.extension :=
  M.extensionFinite
local instance presentationExtensionFinitePresentation (M : Presentation K c) :
    Algebra.FinitePresentation K M.extension :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance
local instance presentationExtensionFlat (M : Presentation K c) : Flat (specMap K M.extension) :=
  (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (RingHom.flat_algebraMap_iff.2 inferInstance)
local instance presentationExtensionSurjective (M : Presentation K c) :
    Surjective (specMap K M.extension) :=
  ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
local instance presentationExtensionLocallyOfFinitePresentation (M : Presentation K c) :
    LocallyOfFinitePresentation (specMap K M.extension) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- Restriction of the actual global class is the sheafification of the saved raw class. -/
theorem Presentation.sheafRepresentation_localPoint (M : Presentation K c)
    {T : Over (Spec (CommRingCat.of K))} (m : T ⟶ Over.mk M.toBase) :
    (ordinaryRelativePicardZeroSheaf c).obj.map
        (DescentAction.coverT (specMap K M.extension) T).op
        (M.sheafRepresentation.homEquiv m) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (Unrigidified.zeroPresheaf c)).app
        (op ((Over.map (specMap K M.extension)).obj
          ((Over.pullback (specMap K M.extension)).obj T)))
        (DescentAction.localPoint (specMap K M.extension) (Unrigidified.zeroPresheaf c)
          M.localPicard.toBase
          (representableByRestrict c M.extension M.localSection M.localRepresentation)
          M.toBase M.comparison M.comparison_over m) := by
  exact DescentAction.globalRepresentation_localPoint (specMap K M.extension)
    (ordinaryRelativePicardZeroSheaf c).obj M.localPicard.toBase
    (DescentAction.sheafifiedLocalRepresentation (specMap K M.extension)
      (Unrigidified.zeroPresheaf c) M.localPicard.toBase
      (representableByRestrict c M.extension M.localSection M.localRepresentation))
    M.toBase M.comparison M.comparison_over
    (DescentAction.isSheafFor_coverT_of_isSheaf (specMap K M.extension)
      (ordinaryRelativePicardZeroSheaf c).obj (ordinaryRelativePicardZeroSheaf c).property)
    ((congrArg
      (fun a => DescentAction.eRel (specMap K M.extension) M.localPicard.toBase
        M.toBase M.comparison M.comparison_over ≫ a)
      (DescentAction.repAct_sheafifiedLocalRepresentation (specMap K M.extension)
        (Unrigidified.zeroPresheaf c) M.localPicard.toBase
        (representableByRestrict c M.extension M.localSection M.localRepresentation))).trans
      M.comparison_action) m

/-- The same compatibility in the actual tensor group sheaf. -/
theorem Presentation.groupSheafRepresentation_localPoint (M : Presentation K c)
    {T : Over (Spec (CommRingCat.of K))} (m : T ⟶ Over.mk M.toBase) :
    (ordinaryRelativePicardZeroGroupSheaf c).obj.map
        (DescentAction.coverT (specMap K M.extension) T).op
        (M.groupSheafRepresentation.homEquiv m) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (Unrigidified.zeroCommGrpPresheaf c)).app
        (op ((Over.map (specMap K M.extension)).obj
          ((Over.pullback (specMap K M.extension)).obj T)))
        (DescentAction.localPoint (specMap K M.extension) (Unrigidified.zeroPresheaf c)
          M.localPicard.toBase
          (representableByRestrict c M.extension M.localSection M.localRepresentation)
          M.toBase M.comparison M.comparison_over m) := by
  let e := ordinaryRelativePicardZeroGroupSheafForgetIso c
  let q := (DescentAction.coverT (specMap K M.extension) T).op
  let T' := (Over.map (specMap K M.extension)).obj
    ((Over.pullback (specMap K M.extension)).obj T)
  let z := DescentAction.localPoint (specMap K M.extension) (Unrigidified.zeroPresheaf c)
    M.localPicard.toBase
    (representableByRestrict c M.extension M.localSection M.localRepresentation)
    M.toBase M.comparison M.comparison_over m
  have hnat : ((ordinaryRelativePicardZeroGroupSheaf c).obj.map q)
      (e.inv.app (op T) (M.sheafRepresentation.homEquiv m)) =
      e.inv.app (op T') ((ordinaryRelativePicardZeroSheaf c).obj.map q
        (M.sheafRepresentation.homEquiv m)) :=
    (ConcreteCategory.congr_hom (e.inv.naturality q)
      (M.sheafRepresentation.homEquiv m)).symm
  have hlocal := congrArg (fun a => e.inv.app (op T') a)
    (M.sheafRepresentation_localPoint m)
  have hunit : e.inv.app (op T')
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (Unrigidified.zeroPresheaf c)).app (op T') z) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (Unrigidified.zeroCommGrpPresheaf c)).app (op T') z :=
    ConcreteCategory.congr_hom (C := Type (u + 1))
      (NatTrans.congr_app
        (sheafComposeIso_hom_fac (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (forget CommGrpCat.{u + 1}) (Unrigidified.zeroCommGrpPresheaf c)) (op T')) z
  exact hnat.trans (hlocal.trans hunit)

variable (K c) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- The existing relative group law classifies tensor multiplication in the actual sheaf. -/
theorem groupSheafRepresentation_mul {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t (toBase K c)) :
    (groupSheafRepresentation K c).homEquiv
        (schemeHomOverToOverHom ((groupLaw K c).mul t x y)) =
      (groupSheafRepresentation K c).homEquiv (schemeHomOverToOverHom x) *
        (groupSheafRepresentation K c).homEquiv (schemeHomOverToOverHom y) := by
  let M := presentation K c
  let H := (ordinaryRelativePicardZeroGroupSheaf c).obj
  have hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (H ⋙ forget CommGrpCat.{u + 1}) :=
    (Presheaf.isSheaf_of_iso_iff (ordinaryRelativePicardZeroGroupSheafForgetIso c)).mpr
      (ordinaryRelativePicardZeroSheaf c).property
  apply Presieve.isSeparatedFor_singleton.1
    (DescentAction.isSheafFor_coverT_of_isSheaf (specMap K M.extension)
      (H ⋙ forget CommGrpCat.{u + 1}) hH (Over.mk t)).isSeparatedFor
  change (H.map (DescentAction.coverT (specMap K M.extension) (Over.mk t)).op) _ =
    (H.map (DescentAction.coverT (specMap K M.extension) (Over.mk t)).op) (_ * _)
  rw [map_mul]
  let e := DescentAction.matchingPointEquiv (specMap K M.extension)
    (Unrigidified.zeroCommGrpPresheaf c) M.localPicard.toBase
    (representableByRestrict c M.extension M.localSection M.localRepresentation)
    M.toBase M.comparison M.comparison_over M.comparison_action t
  let η := (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (Unrigidified.zeroCommGrpPresheaf c)).app
      (op ((Over.map (specMap K M.extension)).obj
        ((Over.pullback (specMap K M.extension)).obj (Over.mk t))))
  have hlocal (z : SchemeHomOver t (toBase K c)) :
      (H.map (DescentAction.coverT (specMap K M.extension) (Over.mk t)).op)
        ((groupSheafRepresentation K c).homEquiv (schemeHomOverToOverHom z)) =
      η (e z).val :=
    M.groupSheafRepresentation_localPoint (schemeHomOverToOverHom z)
  have hmul : η (e ((groupLaw K c).mul t x y)).val = η (e x).val * η (e y).val := by
    change η (e (e.symm (e x * e y))).val = _
    rw [Equiv.apply_symm_apply]
    exact η.hom.map_mul (e x).val (e y).val
  exact (hlocal ((groupLaw K c).mul t x y)).trans
    (hmul.trans (congrArg₂ (· * ·) (hlocal x).symm (hlocal y).symm))

/-- The existing identity classifies the tensor identity in the actual sheaf. -/
theorem groupSheafRepresentation_one {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    (groupSheafRepresentation K c).homEquiv
      (schemeHomOverToOverHom ((groupLaw K c).one t)) = 1 := by
  let M := presentation K c
  let H := (ordinaryRelativePicardZeroGroupSheaf c).obj
  have hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (H ⋙ forget CommGrpCat.{u + 1}) :=
    (Presheaf.isSheaf_of_iso_iff (ordinaryRelativePicardZeroGroupSheafForgetIso c)).mpr
      (ordinaryRelativePicardZeroSheaf c).property
  apply Presieve.isSeparatedFor_singleton.1
    (DescentAction.isSheafFor_coverT_of_isSheaf (specMap K M.extension)
      (H ⋙ forget CommGrpCat.{u + 1}) hH (Over.mk t)).isSeparatedFor
  change (H.map (DescentAction.coverT (specMap K M.extension) (Over.mk t)).op) _ =
    (H.map (DescentAction.coverT (specMap K M.extension) (Over.mk t)).op) 1
  rw [map_one]
  let e := DescentAction.matchingPointEquiv (specMap K M.extension)
    (Unrigidified.zeroCommGrpPresheaf c) M.localPicard.toBase
    (representableByRestrict c M.extension M.localSection M.localRepresentation)
    M.toBase M.comparison M.comparison_over M.comparison_action t
  let η := (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (Unrigidified.zeroCommGrpPresheaf c)).app
      (op ((Over.map (specMap K M.extension)).obj
        ((Over.pullback (specMap K M.extension)).obj (Over.mk t))))
  have hone : η (e ((groupLaw K c).one t)).val = 1 := by
    change η (e (e.symm 1)).val = 1
    rw [Equiv.apply_symm_apply]
    exact η.hom.map_one
  exact (M.groupSheafRepresentation_localPoint
    (schemeHomOverToOverHom ((groupLaw K c).one t))).trans hone

/-- A multiplicative classification for precisely the saved ordinary relative group law. -/
def groupSheafPointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    let _ : Group (SchemeHomOver t (toBase K c)) := (groupLaw K c).pointGroup t
    SchemeHomOver t (toBase K c) ≃*
      (ordinaryRelativePicardZeroGroupSheaf c).obj.obj (op (Over.mk t)) := by
  intro pointGroupStructure
  exact
    { toEquiv := (overHomEquivSchemeHomOver (Over.mk t) (toBase K c)).symm.trans
        (groupSheafRepresentation K c).homEquiv
      map_mul' := groupSheafRepresentation_mul K c t }

end JacobianVarieties.Picard.Unpointed
