/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.OverTotalRepresentation
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Total relative families over a further base

A presheaf over a parameter scheme is viewed on the iterated slice and then
collected over every parameter map. Its actual representing scheme is unchanged;
its structure morphism is composed with the parameter scheme's map to the base.
-/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry

namespace SchemeTheory.WeilRestriction

variable {S B : Scheme.{u}} (b : S ⟶ B) (F : (Over S)ᵒᵖ ⥤ Type w)

/-- The total family on schemes over the further base, with its actual parameter maps. -/
def relativeTotalPresheaf : (Over B)ᵒᵖ ⥤ Type (max u w) :=
  ((Over.iteratedSliceEquiv (Over.mk b)).functor.op ⋙ F).overTotal

/-- The same relative scheme represents the total family over the further base. -/
def relativeTotalRepresentable {W : Over S} (h : F.RepresentableBy W) :
    (relativeTotalPresheaf b F).RepresentableBy ((Over.map b).obj W) := by
  let E := Over.iteratedSliceEquiv (Over.mk b)
  let r : (E.functor.op ⋙ F).RepresentableBy (E.inverse.obj W) :=
    { homEquiv := (E.toAdjunction.homEquiv _ W).symm.trans h.homEquiv
      homEquiv_comp f g := by
        change h.homEquiv ((E.toAdjunction.homEquiv _ W).symm (f ≫ g)) = _
        rw [E.toAdjunction.homEquiv_naturality_left_symm, h.homEquiv_comp]
        rfl }
  exact r.overTotal

/-- The parameter map of a classified total section is the actual structure projection. -/
theorem relativeTotalRepresentable_fst {W : Over S} (h : F.RepresentableBy W)
    {T : Over B} (f : T ⟶ (Over.map b).obj W) :
    ((relativeTotalRepresentable b F h).homEquiv f).1 =
      f ≫ (Over.homMk W.hom rfl : (Over.map b).obj W ⟶ Over.mk b) := rfl

end SchemeTheory.WeilRestriction
