/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups

/-! # Commuting squares of actual represented group morphisms -/

noncomputable section

universe u v w

open CategoryTheory Opposite

namespace SchemeTheory.RepresentedGroups

variable {C : Type u} [Category.{v} C]
  {X Y X' Y' : C} (F G F' G' : Cᵒᵖ ⥤ CommGrpCat.{w})
  (eF : (F ⋙ forget CommGrpCat).RepresentableBy X)
  (eG : (G ⋙ forget CommGrpCat).RepresentableBy Y)
  (eF' : (F' ⋙ forget CommGrpCat).RepresentableBy X')
  (eG' : (G' ⋙ forget CommGrpCat).RepresentableBy Y')

/-- A proved natural-transformation square gives the same square of representing morphisms. -/
theorem mapMorphism_square (a : F ⟶ F') (b : G ⟶ G') (p : F ⟶ G) (p' : F' ⟶ G')
    (h : a ≫ p' = p ≫ b) :
    mapMorphism F F' eF eF' a ≫ mapMorphism F' G' eF' eG' p' =
      mapMorphism F G eF eG p ≫ mapMorphism G G' eG eG' b := by
  apply eG'.homEquiv.injective
  rw [mapMorphism_homEquiv, mapMorphism_homEquiv]
  have ha := mapMorphism_homEquiv F F' eF eF' a (𝟙 X)
  have hp := mapMorphism_homEquiv F G eF eG p (𝟙 X)
  rw [Category.id_comp] at ha hp
  rw [ha, hp]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op X)) (eF.homEquiv (𝟙 X))

end SchemeTheory.RepresentedGroups
