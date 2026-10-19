/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups
import Nyll.SchemeTheory.WeilRestriction.Restriction

/-! # Actual pullback of represented group homomorphisms -/

noncomputable section

universe u w

open CategoryTheory Opposite AlgebraicGeometry

namespace SchemeTheory.RepresentedGroups

variable {S S' : Scheme.{u}} (f : S' ⟶ S) {X Y : Over S}
  (F G : (Over S)ᵒᵖ ⥤ CommGrpCat.{w})
  (eF : (F ⋙ forget CommGrpCat).RepresentableBy X)
  (eG : (G ⋙ forget CommGrpCat).RepresentableBy Y) (a : F ⟶ G)

/-- Restricting the actual natural transformation represents the actual scheme pullback map. -/
theorem mapMorphism_baseChange :
    mapMorphism ((Over.map f).op ⋙ F) ((Over.map f).op ⋙ G)
        (WeilRestriction.representableByBaseChange f eF)
        (WeilRestriction.representableByBaseChange f eG)
        (Functor.whiskerLeft (Over.map f).op a) =
      (Over.pullback f).map (mapMorphism F G eF eG a) := by
  let eF' := WeilRestriction.representableByBaseChange f eF
  let eG' := WeilRestriction.representableByBaseChange f eG
  apply eG'.homEquiv.injective
  have hm := mapMorphism_homEquiv ((Over.map f).op ⋙ F) ((Over.map f).op ⋙ G)
    eF' eG' (Functor.whiskerLeft (Over.map f).op a) (𝟙 ((Over.pullback f).obj X))
  rw [Category.id_comp] at hm
  refine hm.trans ?_
  change (a.app (op ((Over.map f).obj ((Over.pullback f).obj X)))).hom
      (eF.homEquiv (((Over.mapPullbackAdj f).homEquiv _ X).symm (𝟙 _))) =
    eG.homEquiv (((Over.mapPullbackAdj f).homEquiv _ Y).symm
      ((Over.pullback f).map (mapMorphism F G eF eG a)))
  rw [← mapMorphism_homEquiv]
  apply congrArg eG.homEquiv
  have hn := (Over.mapPullbackAdj f).homEquiv_naturality_right_symm
    (𝟙 ((Over.pullback f).obj X)) (mapMorphism F G eF eG a)
  simpa only [Category.id_comp] using hn.symm

end SchemeTheory.RepresentedGroups
