/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups

/-! # Canonical group isomorphisms from represented group presheaf isomorphisms -/

noncomputable section

universe u v w

open CategoryTheory Opposite

namespace SchemeTheory.RepresentedGroups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {X Y : C} (F G : Cᵒᵖ ⥤ CommGrpCat.{w})
  (eF : (F ⋙ forget CommGrpCat).RepresentableBy X)
  (eG : (G ⋙ forget CommGrpCat).RepresentableBy Y)

/-- A natural group isomorphism induces the canonical isomorphism of the actual
represented group objects, with both inverse laws proved on universal sections. -/
def iso (a : F ≅ G) : groupObject F eF ≅ groupObject G eG where
  hom := map F G eF eG a.hom
  inv := map G F eG eF a.inv
  hom_inv_id := by
    apply CommGrp.hom_ext
    apply eF.homEquiv.injective
    change eF.homEquiv
      (mapMorphism F G eF eG a.hom ≫ mapMorphism G F eG eF a.inv) =
        eF.homEquiv (𝟙 X)
    rw [mapMorphism_homEquiv]
    have hm : eG.homEquiv (mapMorphism F G eF eG a.hom) =
        (a.hom.app (op X)).hom (eF.homEquiv (𝟙 X)) := by
      simpa only [Category.id_comp] using
        mapMorphism_homEquiv F G eF eG a.hom (𝟙 X)
    rw [hm]
    exact ConcreteCategory.congr_hom (a.hom_inv_id_app (op X)) (eF.homEquiv (𝟙 X))
  inv_hom_id := by
    apply CommGrp.hom_ext
    apply eG.homEquiv.injective
    change eG.homEquiv
      (mapMorphism G F eG eF a.inv ≫ mapMorphism F G eF eG a.hom) =
        eG.homEquiv (𝟙 Y)
    rw [mapMorphism_homEquiv]
    have hm : eF.homEquiv (mapMorphism G F eG eF a.inv) =
        (a.inv.app (op Y)).hom (eG.homEquiv (𝟙 Y)) := by
      simpa only [Category.id_comp] using
        mapMorphism_homEquiv G F eG eF a.inv (𝟙 Y)
    rw [hm]
    exact ConcreteCategory.congr_hom (a.inv_hom_id_app (op Y)) (eG.homEquiv (𝟙 Y))

end SchemeTheory.RepresentedGroups
