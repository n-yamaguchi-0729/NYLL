/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.OverTotalLocalBijection
import Nyll.SchemeTheory.WeilRestriction.RelativeTotalMap
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! Local bijections of relative families induce local bijections of their total families. -/

universe u w

open CategoryTheory AlgebraicGeometry

namespace SchemeTheory.WeilRestriction

private theorem iteratedSlice_isCocontinuous (J : GrothendieckTopology Scheme.{u})
    {B : Scheme.{u}} (f : Over B) :
    f.iteratedSliceForward.IsCocontinuous ((J.over B).over f) (J.over f.left) :=
  inferInstance

variable (J : GrothendieckTopology Scheme.{u}) {S B : Scheme.{u}} (b : S ⟶ B)
  {F G : (Over S)ᵒᵖ ⥤ Type (max u w)} (a : F ⟶ G)

/-- Local relative preimages give local preimages over the further base. -/
theorem relativeTotalMap_isLocallySurjective [Presheaf.IsLocallySurjective (J.over S) a] :
    Presheaf.IsLocallySurjective (J.over B) (relativeTotalMap b a) := by
  have : (Over.iteratedSliceEquiv (Over.mk b)).functor.IsCocontinuous
      ((J.over B).over (Over.mk b)) (J.over S) :=
    iteratedSlice_isCocontinuous J (Over.mk b)
  have : Presheaf.IsLocallySurjective ((J.over B).over (Over.mk b))
      (Functor.whiskerLeft (Over.iteratedSliceEquiv (Over.mk b)).functor.op a) :=
    Presheaf.isLocallySurjective_whisker ((J.over B).over (Over.mk b)) (J.over S)
      (Over.iteratedSliceEquiv (Over.mk b)).functor a
  exact Functor.overTotalMap_isLocallySurjective (J.over B) _

/-- Local relative equality gives local equality of sections of the total families. -/
theorem relativeTotalMap_isLocallyInjective [Presheaf.IsLocallyInjective (J.over S) a] :
    Presheaf.IsLocallyInjective (J.over B) (relativeTotalMap b a) := by
  have : (Over.iteratedSliceEquiv (Over.mk b)).functor.IsCocontinuous
      ((J.over B).over (Over.mk b)) (J.over S) :=
    iteratedSlice_isCocontinuous J (Over.mk b)
  have : Presheaf.IsLocallyInjective ((J.over B).over (Over.mk b))
      (Functor.whiskerLeft (Over.iteratedSliceEquiv (Over.mk b)).functor.op a) :=
    Presheaf.isLocallyInjective_whisker ((J.over B).over (Over.mk b)) (J.over S)
      (Over.iteratedSliceEquiv (Over.mk b)).functor a
  exact Functor.overTotalMap_isLocallyInjective (J.over B) _

end SchemeTheory.WeilRestriction
