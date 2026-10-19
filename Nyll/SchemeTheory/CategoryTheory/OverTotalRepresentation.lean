/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf

/-! A represented presheaf on a slice has its total presheaf represented by the same carrier. -/

noncomputable section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {S : C}
  {G : (Over S)ᵒᵖ ⥤ Type w} {W : Over S} (h : G.RepresentableBy W)

/-- Forgetting the structure map of the representative represents the total presheaf. -/
def overTotal : G.overTotal.RepresentableBy W.left where
  homEquiv {T} :=
    { toFun k := ⟨k ≫ W.hom, h.homEquiv (Over.homMk k rfl)⟩
      invFun x := (h.homEquiv.symm x.2).left
      left_inv k := congrArg (fun a : Over.mk (k ≫ W.hom) ⟶ W => a.left)
        (h.homEquiv.symm_apply_apply (Over.homMk k rfl))
      right_inv x := by
        let a := h.homEquiv.symm x.2
        apply Functor.OverTotal.ext' a.w
        let k : Over.mk x.1 ⟶ Over.mk (a.left ≫ W.hom) :=
          Over.homMk (𝟙 T) ((Category.id_comp _).trans a.w)
        let b : Over.mk (a.left ≫ W.hom) ⟶ W := Over.homMk a.left rfl
        have hkb : k ≫ b = a := Over.OverMorphism.ext (Category.id_comp a.left)
        exact (h.homEquiv_comp k b).symm.trans
          ((congrArg h.homEquiv hkb).trans (h.homEquiv.apply_symm_apply x.2)) }
  homEquiv_comp {T T'} f g := by
    apply Functor.OverTotal.ext' (Category.assoc f g W.hom)
    let a : Over.mk ((f ≫ g) ≫ W.hom) ⟶ W := Over.homMk (f ≫ g) rfl
    let b : Over.mk (g ≫ W.hom) ⟶ W := Over.homMk g rfl
    let k : Over.mk (f ≫ g ≫ W.hom) ⟶ Over.mk ((f ≫ g) ≫ W.hom) :=
      Over.homMk (𝟙 T) ((Category.id_comp _).trans (Category.assoc f g W.hom))
    let l : Over.mk (f ≫ g ≫ W.hom) ⟶ Over.mk (g ≫ W.hom) := Over.homMk f rfl
    have hka : k ≫ a = l ≫ b := Over.OverMorphism.ext (Category.id_comp (f ≫ g))
    exact (h.homEquiv_comp k a).symm.trans
      ((congrArg h.homEquiv hka).trans (h.homEquiv_comp l b))

end CategoryTheory.Functor.RepresentableBy
