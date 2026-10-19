/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! # Multiplicative point equivalences supplied by an adjunction -/

noncomputable section

universe u v u' v'

open CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  {L : C ⥤ D} {R : D ⥤ C} [R.Monoidal]

/-- The adjunction point equivalence preserves the actual monoid laws when the
right adjoint is monoidal. No monoidal structure on the left adjoint is needed. -/
def homMulEquiv (adj : L ⊣ R) (X : C) (M : D) [MonObj M] :
    (L.obj X ⟶ M) ≃* (X ⟶ R.obj M) where
  toEquiv := adj.homEquiv X M
  map_mul' f g := by
    calc
      (adj.homEquiv X M).toFun (f * g) = adj.unit.app X ≫ R.map (f * g) :=
        adj.homEquiv_unit X M (f * g)
      _ = adj.unit.app X ≫ (R.map f * R.map g) :=
        congrArg (fun h => adj.unit.app X ≫ h) (R.map_mul f g)
      _ = (adj.unit.app X ≫ R.map f) * (adj.unit.app X ≫ R.map g) :=
        MonObj.comp_mul _ _ _
      _ = (adj.homEquiv X M).toFun f * (adj.homEquiv X M).toFun g :=
        congrArg₂ (fun a b => a * b)
          (adj.homEquiv_unit X M f).symm (adj.homEquiv_unit X M g).symm

/-- The adjunction point equivalence intertwines a monoid action with the
actual action transported by the right adjoint. -/
theorem homEquiv_modObj_smul (adj : L ⊣ R) (X : C) (M P : D)
    [MonObj M] [ModObj M P] (m : L.obj X ⟶ M) (p : L.obj X ⟶ P) :
    let _ : ModObj (R.obj M) (R.obj P) := R.modObjObj M P
    adj.homEquiv X P (m • p) = adj.homEquiv X M m • adj.homEquiv X P p := by
  intro transportedAction
  calc
    adj.homEquiv X P (m • p) = adj.unit.app X ≫ R.map (m • p) :=
      adj.homEquiv_unit X P (m • p)
    _ = adj.unit.app X ≫ (R.map m • R.map p) :=
      congrArg (fun h => adj.unit.app X ≫ h) (R.map_modObj_smul M P m p)
    _ = (adj.unit.app X ≫ R.map m) • (adj.unit.app X ≫ R.map p) :=
      ModObj.comp_smul _ _ _
    _ = adj.homEquiv X M m • adj.homEquiv X P p :=
      congrArg₂ (fun a b => a • b)
        (adj.homEquiv_unit X M m).symm (adj.homEquiv_unit X P p).symm

/-- Adjoint points have the transported difference: the same actual
group element carries the second torsor point to the first. -/
theorem homEquiv_torsor_difference (adj : L ⊣ R) (X : C) (M P : D)
    [MonObj M] [ModObj M P] [IsIso (ModObj.leftSMul M P)]
    (x y : L.obj X ⟶ P) :
    let _ : ModObj (R.obj M) (R.obj P) := R.modObjObj M P
    let _ : IsIso (ModObj.leftSMul (R.obj M) (R.obj P)) :=
      R.isIso_leftSMul_modObjObj M P
    adj.homEquiv X M (SchemeTheory.PointedTorsor.difference (G := M) x y) =
      SchemeTheory.PointedTorsor.difference (G := R.obj M)
        (adj.homEquiv X P x) (adj.homEquiv X P y) := by
  intro transportedAction transportedTorsor
  apply SchemeTheory.PointedTorsor.difference_unique
  rw [← adj.homEquiv_modObj_smul, SchemeTheory.PointedTorsor.difference_smul]

end CategoryTheory.Adjunction
