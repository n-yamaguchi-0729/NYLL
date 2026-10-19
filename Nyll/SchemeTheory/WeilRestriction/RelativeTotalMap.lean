/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.OverTotalMap
import Nyll.SchemeTheory.WeilRestriction.RelativeTotal

/-! Natural maps from a relative family give maps from its total family over the further base. -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry

namespace SchemeTheory.WeilRestriction

variable {S B : Scheme.{u}} (b : S ⟶ B)

/-- A natural transformation of relative families induces one of their actual total families. -/
def relativeTotalMap {F G : (Over S)ᵒᵖ ⥤ Type (max u w)} (a : F ⟶ G) :
    relativeTotalPresheaf b F ⟶ relativeTotalPresheaf b G :=
  Functor.overTotalMap (Functor.whiskerLeft (Over.iteratedSliceEquiv (Over.mk b)).functor.op a)

/-- The iterated-slice equivalence preserves the actual scheme over the further base. -/
def relativeTotalForgetIso :
    (Over.iteratedSliceEquiv (Over.mk b)).functor ⋙ Over.map b ≅ Over.forget (Over.mk b) := by
  let E := Over.iteratedSliceEquiv (Over.mk b)
  have hforget : E.inverse ⋙ Over.forget (Over.mk b) = Over.map b :=
    Over.iteratedSliceBackward_forget (Over.mk b)
  rw [← hforget]
  exact (Functor.associator E.functor E.inverse (Over.forget (Over.mk b))).symm ≪≫
    Functor.isoWhiskerRight E.unitIso.symm (Over.forget (Over.mk b)) ≪≫
      Functor.leftUnitor (Over.forget (Over.mk b))

/-- The actual slice comparison defines a natural comparison of total families. -/
def relativeTotalDesc {F : (Over S)ᵒᵖ ⥤ Type (max u w)}
    {Q : (Over B)ᵒᵖ ⥤ Type (max u w)} (a : F ⟶ (Over.map b).op ⋙ Q) :
    relativeTotalPresheaf b F ⟶ Q :=
  Functor.overTotalDesc
    (Functor.whiskerLeft (Over.iteratedSliceEquiv (Over.mk b)).functor.op a ≫
      (Functor.associator (Over.iteratedSliceEquiv (Over.mk b)).functor.op
        (Over.map b).op Q).inv ≫
      (Functor.isoWhiskerRight (NatIso.op (relativeTotalForgetIso b).symm) Q).hom)

end SchemeTheory.WeilRestriction
