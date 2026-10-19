/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Constant coefficients and coefficient functors

The canonical constant-sheaf comparison for a coefficient functor carries
constant-sheaf adjunction units to the corresponding units. The proof uses
the defining sheafification comparison and its actual unit square.
-/

noncomputable section

universe uC vC uA vA uB vB

open CategoryTheory Limits Opposite

namespace EtaleCohomology.Sites

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  (V : A ⥤ B) [J.PreservesSheafification V] [J.HasSheafCompose V]

/-- The canonical comparison between constant sheaves and a coefficient
functor intertwines their adjunction units at every terminal object. -/
theorem constantCommuteCompose_unit {T : C} (hT : IsTerminal T) (M : A) :
    V.map ((constantSheafAdj J A hT).unit.app M) ≫
        ((constantCommuteCompose J V).hom.app M).hom.app (op T) =
      (constantSheafAdj J B hT).unit.app (V.obj M) := by
  have huA : (constantSheafAdj J A hT).unit.app M =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) := by
    rw [constantSheafAdj, Adjunction.comp_unit_app]
    change 𝟙 M ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) = _
    exact Category.id_comp _
  have huB : (constantSheafAdj J B hT).unit.app (V.obj M) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (V.obj M))).app (op T) := by
    rw [constantSheafAdj, Adjunction.comp_unit_app]
    change 𝟙 (V.obj M) ≫
      (toSheafify J ((Functor.const Cᵒᵖ).obj (V.obj M))).app (op T) = _
    exact Category.id_comp _
  have hp : Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M)) V ≫
      ((constantCommuteCompose J V).hom.app M).hom =
        (Functor.constComp Cᵒᵖ M V).hom ≫
          toSheafify J ((Functor.const Cᵒᵖ).obj (V.obj M)) := by
    change Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M)) V ≫
        (sheafifyComposeIso J V ((Functor.const Cᵒᵖ).obj M)).inv ≫
          sheafifyMap J (Functor.constComp Cᵒᵖ M V).hom =
      (Functor.constComp Cᵒᵖ M V).hom ≫
        toSheafify J ((Functor.const Cᵒᵖ).obj (V.obj M))
    rw [← Category.assoc, CategoryTheory.sheafComposeIso_inv_fac]
    exact (CategoryTheory.toSheafify_naturality J
      (Functor.constComp Cᵒᵖ M V).hom).symm
  have ht := congrArg (fun φ => φ.app (op T)) hp
  change V.map ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T)) ≫
      ((constantCommuteCompose J V).hom.app M).hom.app (op T) =
        𝟙 (V.obj M) ≫
          (toSheafify J ((Functor.const Cᵒᵖ).obj (V.obj M))).app (op T) at ht
  rw [huA, huB]
  exact ht.trans (Category.id_comp _)

end EtaleCohomology.Sites
