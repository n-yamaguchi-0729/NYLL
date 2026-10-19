/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups

/-! # The identity under a represented group equivalence -/

noncomputable section

universe u v w

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace SchemeTheory.RepresentedGroups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {X : C} (F : Cᵒᵖ ⥤ CommGrpCat.{w})
  (eF : (F ⋙ forget CommGrpCat).RepresentableBy X)

/-- The actual identity of the represented group is classified by the identity section. -/
theorem homEquiv_one (T : C) :
    eF.homEquiv (1 : T ⟶ (groupObject F eF).X) = 1 := by
  let : CommGrpObj X := CommGrpObj.ofRepresentableBy X F eF
  exact (pointEquiv F eF T).map_one

end SchemeTheory.RepresentedGroups
