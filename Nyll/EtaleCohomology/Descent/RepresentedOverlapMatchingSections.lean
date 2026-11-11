/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.RepresentableGlobalSectionsPullback

/-!
# Original matching global sections of a represented overlap

The actual sheaf inverse-image section maps and the specified represented
overlap give precisely the two literal scheme section lifts. This
identifies the original H⁰ matching equation with the equation used by
the split action, without introducing a separate matching object.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology.SetSheafDescent

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (W : Y.Etale)
  (η : (etaleBaseChange (pullback.fst q q)).obj W ≅
    (etaleBaseChange (pullback.snd q q)).obj W)

/-- The specified represented overlap, through the existing actual
inverse-image comparisons. -/
def representedOverlapIso :
    (etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W) ≅
      (etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W) :=
  etaleSetPullbackYonedaObjIso (pullback.fst q q) W ≪≫
    (pullback q q).smallEtaleTopology.yoneda.mapIso η ≪≫
      (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).symm

/-- The original H⁰ matching equation is the literal equality of the
first section transported by the overlap and the second section. -/
theorem represented_globalSections_matching_iff
    (u : (Scheme.Etale.mk (𝟙 Y) : Y.Etale) ⟶ W) :
    (representedOverlapIso q W η).hom.hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback q q))))
        (etaleSetPullbackGlobalSectionsMap (pullback.fst q q)
          (Y.smallEtaleTopology.yoneda.obj W) u) =
      etaleSetPullbackGlobalSectionsMap (pullback.snd q q)
        (Y.smallEtaleTopology.yoneda.obj W) u ↔
    pullback.lift (pullback.fst q q ≫ u.left) (𝟙 (pullback q q))
        ((Category.assoc _ u.left W.hom).trans
          ((congrArg (fun k => pullback.fst q q ≫ k) u.w).trans
            ((Category.comp_id _).trans (Category.id_comp _).symm))) ≫ η.hom.left =
      pullback.lift (pullback.snd q q ≫ u.left) (𝟙 (pullback q q))
        ((Category.assoc _ u.left W.hom).trans
          ((congrArg (fun k => pullback.snd q q ≫ k) u.w).trans
            ((Category.comp_id _).trans (Category.id_comp _).symm))) := by
  let D := pullback q q
  let I : D.Etale := Scheme.Etale.mk (𝟙 D)
  let β₁ := etaleSetPullbackYonedaObjIso (pullback.fst q q) W
  let β₂ := etaleSetPullbackYonedaObjIso (pullback.snd q q) W
  let E₂ := ((sheafSections D.smallEtaleTopology (Type u)).obj (op I)).mapIso β₂
  let t₁ := etaleBaseChangeLift (U := I) (pullback.fst q q) (pullback.fst q q ≫ u.left)
    ((Category.assoc _ u.left W.hom).trans
      ((congrArg (fun k => pullback.fst q q ≫ k) u.w).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
  let t₂ := etaleBaseChangeLift (U := I) (pullback.snd q q) (pullback.snd q q ≫ u.left)
    ((Category.assoc _ u.left W.hom).trans
      ((congrArg (fun k => pullback.snd q q ≫ k) u.w).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
  have hs : (representedOverlapIso q W η).hom ≫ β₂.hom =
      β₁.hom ≫ D.smallEtaleTopology.yoneda.map η.hom := by
    change ((β₁.hom ≫ D.smallEtaleTopology.yoneda.map η.hom) ≫ β₂.inv) ≫ β₂.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hleft :
      E₂.hom ((representedOverlapIso q W η).hom.hom.app (op I)
        (etaleSetPullbackGlobalSectionsMap (pullback.fst q q)
          (Y.smallEtaleTopology.yoneda.obj W) u)) = t₁ ≫ η.hom := by
    have he := ConcreteCategory.congr_hom
      (congrArg (fun r => r.hom.app (op I)) hs)
      (etaleSetPullbackGlobalSectionsMap (pullback.fst q q)
        (Y.smallEtaleTopology.yoneda.obj W) u)
    change E₂.hom ((representedOverlapIso q W η).hom.hom.app (op I)
        (etaleSetPullbackGlobalSectionsMap (pullback.fst q q)
          (Y.smallEtaleTopology.yoneda.obj W) u)) =
      β₁.hom.hom.app (op I)
        (etaleSetPullbackGlobalSectionsMap (pullback.fst q q)
          (Y.smallEtaleTopology.yoneda.obj W) u) ≫ η.hom at he
    exact he.trans (congrArg (fun r => r ≫ η.hom)
      (etaleSetPullbackGlobalSectionsMap_yoneda (pullback.fst q q) W u))
  have hright :
      E₂.hom (etaleSetPullbackGlobalSectionsMap (pullback.snd q q)
        (Y.smallEtaleTopology.yoneda.obj W) u) = t₂ :=
    etaleSetPullbackGlobalSectionsMap_yoneda (pullback.snd q q) W u
  constructor
  · intro he
    have hp := congrArg E₂.hom he
    rw [hleft, hright] at hp
    exact congrArg (fun r => r.left) hp
  · intro he
    have hh : t₁ ≫ η.hom = t₂ := MorphismProperty.Over.Hom.ext he
    exact E₂.toEquiv.injective (hleft.trans (hh.trans hright.symm))

end EtaleCohomology.SetSheafDescent
