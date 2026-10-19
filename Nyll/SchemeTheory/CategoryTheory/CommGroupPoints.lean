/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupTargetIso

/-! # Actual commutative-group points and reconstruction from their natural coordinates -/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace SchemeTheory.CommGroupPoints

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- The commutative groups of actual points of a commutative group object. -/
def points (G : CommGrp C) : Cᵒᵖ ⥤ CommGrpCat.{v} where
  obj T := CommGrpCat.of (T.unop ⟶ G.X)
  map f := CommGrpCat.ofHom ((yonedaGrpObj G.X).map f).hom
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Category.id_comp x
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Category.assoc _ _ _

/-- The point presheaf retains its tautological representation on the given object. -/
def representable (G : CommGrp C) :
    (points G ⋙ forget CommGrpCat).RepresentableBy G.X where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- Natural multiplicative point coordinates give an isomorphism of the actual group objects. -/
def isoOfPointEquiv (G H : CommGrp C)
    (e : ∀ T : C, (T ⟶ G.X) ≃* (T ⟶ H.X))
    (hn : ∀ {T T' : C} (f : T ⟶ T') (x : T' ⟶ G.X), e T (f ≫ x) = f ≫ e T' x) :
    G ≅ H := by
  let r : (points G ⋙ forget CommGrpCat).RepresentableBy H.X :=
    { homEquiv := fun {T} => (e T).symm.toEquiv
      homEquiv_comp := fun {T T'} f x => by
        apply (e T).injective
        exact ((e T).apply_symm_apply (f ≫ x)).trans
          ((congrArg (fun y => f ≫ y) ((e T').apply_symm_apply x)).symm.trans
            (hn f ((e T').symm x)).symm) }
  exact (RepresentedGroups.isoToGroup (points G) (representable G) G
      (representable G) (fun _ _ _ => rfl)).symm ≪≫
    RepresentedGroups.isoToGroup (points G) (representable G) H r
      (fun T f g => (e T).symm.map_mul f g)

/-- Points of the actual product group carry the componentwise multiplication. -/
def productPointEquiv (G H : CommGrp C) (T : C) :
    (T ⟶ G.X ⊗ H.X) ≃* ((T ⟶ G.X) × (T ⟶ H.X)) where
  toEquiv := homEquivToProd
  map_mul' f g :=
    Prod.ext (MonObj.mul_comp f g (fst G.X H.X)) (MonObj.mul_comp f g (snd G.X H.X))

end SchemeTheory.CommGroupPoints
