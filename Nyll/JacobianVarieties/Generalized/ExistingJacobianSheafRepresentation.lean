/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.Unpointed.UnpointedJacobian
import Nyll.JacobianVarieties.Generalized.PicardZeroForgetfulGroup
import Nyll.AlgebraicCurves.Geometry.Descent.SheafifiedLocalRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.FppfCoverRepresentation
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups

/-!
# The existing unpointed Jacobian represents the actual ordinary Picard sheaf

The saved unpointed Jacobian already retains its effective descent presentation.
Sheafification is an isomorphism on its represented finite-extension slice and
preserves the canonical action. The same carrier therefore represents the
actual fppf sheaf, with no claim that the unpointed raw presheaf is a sheaf.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.GeneralizedJacobian NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}

/-- The same effective descent carrier represents the actual ordinary Picard-zero sheaf. -/
def Presentation.sheafRepresentation (M : Presentation K c) :
    (ordinaryRelativePicardZeroSheaf c).obj.RepresentableBy (Over.mk M.toBase) := by
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  have : Module.Finite K M.extension := M.extensionFinite
  have : Algebra.FinitePresentation K M.extension :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Flat (specMap K M.extension) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (specMap K M.extension) :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  have : LocallyOfFinitePresentation (specMap K M.extension) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let F := Unrigidified.zeroPresheaf c
  let eRaw := representableByRestrict c M.extension M.localSection M.localRepresentation
  let eSheaf := DescentAction.sheafifiedLocalRepresentation
    (specMap K M.extension) F M.localPicard.toBase eRaw
  have hc : DescentAction.eRel (specMap K M.extension) M.localPicard.toBase M.toBase
        M.comparison M.comparison_over ≫
      DescentAction.repAct (specMap K M.extension) (ordinaryRelativePicardZeroSheaf c).obj
        M.localPicard.toBase eSheaf =
      (DescentAction.canonical (specMap K M.extension) M.toBase).act ≫ M.comparison.hom := by
    exact (congrArg
      (fun a => DescentAction.eRel (specMap K M.extension) M.localPicard.toBase
        M.toBase M.comparison M.comparison_over ≫ a)
      (DescentAction.repAct_sheafifiedLocalRepresentation (specMap K M.extension)
        F M.localPicard.toBase eRaw)).trans M.comparison_action
  exact DescentAction.globalRepresentation (specMap K M.extension)
    (ordinaryRelativePicardZeroSheaf c).obj M.localPicard.toBase eSheaf
    M.toBase M.comparison M.comparison_over
    (DescentAction.isSheafFor_coverT_of_isSheaf (specMap K M.extension)
      (ordinaryRelativePicardZeroSheaf c).obj (ordinaryRelativePicardZeroSheaf c).property) hc

/-- The group sheaf has the same existing carrier and the same descended universal class. -/
def Presentation.groupSheafRepresentation (M : Presentation K c) :
    ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (Over.mk M.toBase) :=
  M.sheafRepresentation.ofIso (ordinaryRelativePicardZeroGroupSheafForgetIso c).symm

/-- The existing carrier, equipped using its actual ordinary tensor group sheaf. -/
def Presentation.sheafGroupScheme (M : Presentation K c) :
    CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject (ordinaryRelativePicardZeroGroupSheaf c).obj
    M.groupSheafRepresentation

variable (K c) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- The already chosen unpointed Jacobian represents the actual ordinary group sheaf. -/
def groupSheafRepresentation :
    ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (Over.mk (toBase K c)) :=
  (presentation K c).groupSheafRepresentation

/-- The tensor sheaf group on the already chosen unpointed Jacobian carrier. -/
def sheafGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  (presentation K c).sheafGroupScheme

end JacobianVarieties.Picard.Unpointed
