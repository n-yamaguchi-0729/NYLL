/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups

/-! # Identifying a represented group with a given actual group object -/

noncomputable section

universe u v w

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace SchemeTheory.RepresentedGroups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {X : C} (F : Cᵒᵖ ⥤ CommGrpCat.{w})
  (eF : (F ⋙ forget CommGrpCat).RepresentableBy X)
  (G : CommGrp C) (eG : (F ⋙ forget CommGrpCat).RepresentableBy G.X)
  (hmul : ∀ (T : C) (f g : T ⟶ G.X),
    eG.homEquiv (f * g) = eG.homEquiv f * eG.homEquiv g)

/-- A multiplicative representing dictionary identifies the represented group with the
actual target group, including its original multiplication and inverse. -/
def isoToGroup : groupObject F eF ≅ G := by
  let : CommGrpObj X := CommGrpObj.ofRepresentableBy X F eF
  let a := eF.uniqueUpToIso eG
  let p (T : C) : (T ⟶ G.X) ≃* F.obj (op T) :=
    { toEquiv := eG.homEquiv, map_mul' := hmul T }
  have ha {T : C} (f : T ⟶ X) : eG.homEquiv (f ≫ a.hom) = eF.homEquiv f := by
    change eG.homEquiv (f ≫ eG.homEquiv.symm (eF.homEquiv (𝟙 X))) = _
    rw [eG.homEquiv_comp, Equiv.apply_symm_apply, ← eF.homEquiv_comp, Category.comp_id]
  have hone (T : C) : (1 : T ⟶ X) ≫ a.hom = (1 : T ⟶ G.X) := by
    apply (p T).injective
    change eG.homEquiv (1 ≫ a.hom) = (p T) 1
    rw [ha, (p T).map_one]
    exact (pointEquiv F eF T).map_one
  have hproduct (T : C) (f g : T ⟶ X) :
      (f * g) ≫ a.hom = (f ≫ a.hom) * (g ≫ a.hom) := by
    apply (p T).injective
    change eG.homEquiv ((f * g) ≫ a.hom) =
      eG.homEquiv ((f ≫ a.hom) * (g ≫ a.hom))
    rw [ha, hmul, ha, ha]
    exact (pointEquiv F eF T).map_mul f g
  have : IsMonHom a.hom :=
    { one_hom := by
        simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using hone (𝟙_ C)
      mul_hom := by
        simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
          using hproduct (X ⊗ X) (fst X X) (snd X X) }
  exact CommGrp.mkIso' a

end SchemeTheory.RepresentedGroups
