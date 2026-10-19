/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf

/-! A natural map on a slice descends to its actual total presheaf. -/

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {S : C}
  {G : (Over S)ᵒᵖ ⥤ Type (max v w)} {F : Cᵒᵖ ⥤ Type (max v w)}

/-- A map of relative families preserves the actual parameter map in their total families. -/
def overTotalMap {H : (Over S)ᵒᵖ ⥤ Type (max v w)} (a : G ⟶ H) :
    G.overTotal ⟶ H.overTotal where
  app T := TypeCat.ofHom (fun x => ⟨x.1, a.app (op (Over.mk x.1)) x.2⟩)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    exact congrArg
      (fun z : H.obj (op (Over.mk (f.unop ≫ x.1))) =>
        (⟨f.unop ≫ x.1, z⟩ : H.OverTotal T'.unop))
      (a.naturality_apply
        (Over.homMk f.unop rfl : Over.mk (f.unop ≫ x.1) ⟶ Over.mk x.1).op x.2)

/-- Evaluate a slice comparison on the parameter map of each total-family element. -/
def overTotalDesc (a : G ⟶ (Over.forget S).op ⋙ F) : G.overTotal ⟶ F where
  app T := TypeCat.ofHom (fun x => a.app (op (Over.mk x.1)) x.2)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    exact ConcreteCategory.congr_hom
      (a.naturality (Over.homMk f.unop rfl : Over.mk (f.unop ≫ x.1) ⟶ Over.mk x.1).op)
      x.2

end CategoryTheory.Functor

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {F Q : Cᵒᵖ ⥤ Type w} {W : C}

/-- A natural comparison on a represented family is determined by its universal value. -/
theorem natTrans_homEquiv (h : F.RepresentableBy W) (a : F ⟶ Q) {T : C} (f : T ⟶ W) :
    a.app (op T) (h.homEquiv f) = Q.map f.op (a.app (op W) (h.homEquiv (𝟙 W))) :=
  (congrArg (a.app (op T)) (h.homEquiv_eq f)).trans
    (a.naturality_apply f.op (h.homEquiv (𝟙 W)))

end CategoryTheory.Functor.RepresentableBy
