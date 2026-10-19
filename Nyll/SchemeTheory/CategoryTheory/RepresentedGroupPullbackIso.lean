/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupTargetIso
import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints
import Nyll.SchemeTheory.WeilRestriction.Restriction
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # The group dictionary for actual pullback of a represented group -/

noncomputable section

universe u w

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace SchemeTheory.RepresentedGroups

variable {S S' : Scheme.{u}} (f : S' ⟶ S) {X : Over S}
  (F : (Over S)ᵒᵖ ⥤ CommGrpCat.{w})
  (eF : (F ⋙ forget CommGrpCat).RepresentableBy X)

/-- The literal pullback group and the represented restricted group have the same
actual carrier and canonically isomorphic group laws. -/
def groupObjectPullbackIso :
    (Over.pullback f).mapCommGrp.obj (groupObject F eF) ≅
      groupObject ((Over.map f).op ⋙ F)
        (WeilRestriction.representableByBaseChange f eF) := by
  let : CommGrpObj X := CommGrpObj.ofRepresentableBy X F eF
  apply (isoToGroup ((Over.map f).op ⋙ F)
    (WeilRestriction.representableByBaseChange f eF)
    ((Over.pullback f).mapCommGrp.obj (groupObject F eF))
    (WeilRestriction.representableByBaseChange f eF) ?_).symm
  intro T a b
  change T ⟶ (Over.pullback f).obj X at a b
  change eF.homEquiv (((Over.mapPullbackAdj f).homMulEquiv T X).symm (a * b)) =
    eF.homEquiv (((Over.mapPullbackAdj f).homMulEquiv T X).symm a) *
      eF.homEquiv (((Over.mapPullbackAdj f).homMulEquiv T X).symm b)
  exact (congrArg eF.homEquiv
    (((Over.mapPullbackAdj f).homMulEquiv T X).symm.map_mul a b)).trans
      ((pointEquiv F eF ((Over.map f).obj T)).map_mul _ _)

end SchemeTheory.RepresentedGroups
