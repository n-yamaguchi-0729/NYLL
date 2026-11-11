/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The composite transpose of an inverse image of the counit

This is the category-independent form of the calculation used for the
first matching arrow. Both overlap projections use the same calculation.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace EtaleCohomology

/-- Transposing the image of the first counit under the composite
adjunction gives the first direct image of the second unit. -/
theorem adjunction_composite_homEquiv_map_counit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {S : E ⥤ D}
    (A : L ⊣ R) (B : M ⊣ S) (F : D) :
    (A.comp B).homEquiv (R.obj F) (M.obj F) (M.map (A.counit.app F)) =
      R.map (B.unit.app F) := by
  have hB : B.homEquiv (L.obj (R.obj F)) (M.obj F)
      (M.map (A.counit.app F)) = A.counit.app F ≫ B.unit.app F := by
    exact (congrArg (B.homEquiv _ _) (Category.comp_id _).symm).trans
      ((B.homEquiv_naturality_left (A.counit.app F) (𝟙 _)).trans
        (congrArg (fun a => A.counit.app F ≫ a) (B.homEquiv_id F)))
  have hA : A.homEquiv _ _ (A.counit.app F) = 𝟙 _ :=
    (congrArg (A.homEquiv _ _) (A.homEquiv_symm_id F).symm).trans
      ((A.homEquiv _ _).apply_symm_apply (𝟙 _))
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
  exact (congrArg (A.homEquiv _ _) hB).trans
    ((A.homEquiv_naturality_right (A.counit.app F) (B.unit.app F)).trans
      ((congrArg (fun a => a ≫ R.map (B.unit.app F)) hA).trans
        (Category.id_comp _)))

end EtaleCohomology
