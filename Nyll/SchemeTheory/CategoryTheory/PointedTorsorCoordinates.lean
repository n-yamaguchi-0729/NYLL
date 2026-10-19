/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Coordinates and scalar extension of categorical torsors

A monoidal functor transports the actual action and its torsor isomorphism.
A chosen point then supplies the coordinate morphism and trivialization.
-/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchemeTheory.PointedTorsor

variable {B : Type u} [Category.{v} B] [CartesianMonoidalCategory B]
  {G P : B} [MonObj G] [ModObj G P] [IsIso (ModObj.leftSMul G P)]

/-- Difference is the first projection of the actual inverse torsor morphism. -/
def difference {T : B} (x y : T ⟶ P) : T ⟶ G :=
  lift x y ≫ inv (ModObj.leftSMul G P) ≫ fst G P

/-- The actual difference carries the second point to the first one. -/
theorem difference_smul {T : B} (x y : T ⟶ P) : difference (G := G) x y • y = x := by
  let z := lift x y ≫ inv (ModObj.leftSMul G P)
  have hz : z ≫ ModObj.leftSMul G P = lift x y := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hs : z ≫ snd G P = y := by
    have h := congrArg (fun f => f ≫ snd P P) hz
    simpa only [Category.assoc, ModObj.leftSMul_snd, lift_snd] using h
  have hf : z ≫ γ[G, P] = x := by
    have h := congrArg (fun f => f ≫ fst P P) hz
    simpa only [Category.assoc, ModObj.leftSMul_fst, lift_fst] using h
  rw [difference, ← Category.assoc, CategoryTheory.Hom.smul_def]
  change lift (z ≫ fst G P) y ≫ γ[G, P] = x
  rw [← hs, ← comp_lift, lift_fst_snd, Category.comp_id]
  exact hf

/-- The inverse scheme morphism gives the unique element translating the two points. -/
theorem difference_unique {T : B} (x y : T ⟶ P) (g : T ⟶ G) (h : g • y = x) :
    g = difference (G := G) x y :=
  ((ModObj.isIso_leftSMul_iff (M := G) (X := P)).mp inferInstance T y x).unique
    h (difference_smul x y)

/-- Difference of actual points is natural under every change of test object. -/
theorem difference_naturality {T T' : B} (f : T' ⟶ T) (x y : T ⟶ P) :
    f ≫ difference (G := G) x y = difference (f ≫ x) (f ≫ y) :=
  difference_unique _ _ _ ((ModObj.comp_smul f (difference x y) y).symm.trans
    (congrArg (fun a => f ≫ a) (difference_smul x y)))

/-- The coordinate morphism furnished by an actual point of the torsor. -/
def coordinate (p : 𝟙_ B ⟶ P) : P ⟶ G :=
  difference (𝟙 P) (toUnit P ≫ p)

/-- Every point is recovered by the action of its coordinate on the basepoint. -/
theorem coordinate_smul (p : 𝟙_ B ⟶ P) {T : B} (x : T ⟶ P) :
    (x ≫ coordinate (G := G) p) • (toUnit T ≫ p) = x := by
  have h := congrArg (fun a => x ≫ a) (difference_smul (G := G) (𝟙 P) (toUnit P ≫ p))
  simpa only [coordinate, ModObj.comp_smul, Category.assoc, comp_toUnit_assoc,
    Category.comp_id] using h

/-- The coordinate is the unique element taking the actual basepoint to the specified point. -/
theorem coordinate_unique (p : 𝟙_ B ⟶ P) {T : B} (x : T ⟶ P) (g : T ⟶ G)
    (h : g • (toUnit T ≫ p) = x) : g = x ≫ coordinate (G := G) p :=
  ((ModObj.isIso_leftSMul_iff (M := G) (X := P)).mp inferInstance T
    (toUnit T ≫ p) x).unique h (coordinate_smul p x)

/-- The basepoint has identity coordinate on every test object. -/
theorem coordinate_basepoint (p : 𝟙_ B ⟶ P) (T : B) :
    (toUnit T ≫ p) ≫ coordinate (G := G) p = 1 :=
  (coordinate_unique p _ 1 (one_smul _ _)).symm

/-- Coordinates intertwine the actual action and the actual multiplication. -/
theorem coordinate_smul_eq (p : 𝟙_ B ⟶ P) {T : B} (g : T ⟶ G) (x : T ⟶ P) :
    (g • x) ≫ coordinate p = g * (x ≫ coordinate p) :=
  (coordinate_unique p (g • x) (g * (x ≫ coordinate p)) (by
    rw [mul_smul, coordinate_smul])).symm

/-- A chosen point trivializes the actual torsor by morphisms in the original category. -/
def trivialization (p : 𝟙_ B ⟶ P) : P ≅ G where
  hom := coordinate p
  inv := (𝟙 G) • (toUnit G ≫ p)
  hom_inv_id := by
    rw [ModObj.comp_smul, Category.comp_id, comp_toUnit_assoc]
    simpa only [Category.id_comp] using coordinate_smul p (𝟙 P)
  inv_hom_id := by
    rw [coordinate_smul_eq, coordinate_basepoint, mul_one]


/-- A group acting on itself by its actual multiplication is a torsor.
The unique transporter of two parameter points is their quotient. -/
theorem isIso_leftSMul_regular (H : B) [GrpObj H] :
    let _ : ModObj H H := ModObj.regular H
    IsIso (ModObj.leftSMul H H) := by
  intro regularAction
  apply (ModObj.isIso_leftSMul_iff (M := H) (X := H)).mpr
  intro T x y
  refine ⟨y / x, ?_, ?_⟩
  · change (y / x) * x = y
    exact div_mul_cancel y x
  · intro g hg
    change g * x = y at hg
    exact eq_div_of_mul_eq' hg

/-- Coordinates at the identity of the regular group torsor are the
identity morphism, with the same actual multiplication throughout. -/
theorem coordinate_regular_unit (H : B) [GrpObj H] :
    let _ : ModObj H H := ModObj.regular H
    let _ : IsIso (ModObj.leftSMul H H) := isIso_leftSMul_regular H
    coordinate (G := H) η[H] = 𝟙 H := by
  intro regularAction regularTorsor
  have h := coordinate_unique (G := H) η[H] (𝟙 H) (𝟙 H) (by
    change (𝟙 H) * 1 = 𝟙 H
    exact mul_one _)
  simpa only [Category.id_comp] using h.symm

end SchemeTheory.PointedTorsor

namespace CategoryTheory.Functor

universe u' v'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (G P : C) [MonObj G] [ModObj G P]

open scoped CategoryTheory.Obj

/-- Transport the actual action using the monoidal functor's product
comparison. This is explicit data, so it does not install competing actions. -/
abbrev modObjObj : ModObj (F.obj G) (F.obj P) where
  smul := LaxMonoidal.μ F G P ≫ F.map γ[G, P]
  one_smul := by
    change (LaxMonoidal.ε F ≫ F.map η[G]) ▷ F.obj P ≫
      (LaxMonoidal.μ F G P ≫ F.map γ[G, P]) = (λ_ (F.obj P)).hom
    simp only [comp_whiskerRight, Category.assoc, LaxMonoidal.μ_natural_left_assoc,
      ← F.map_comp, ModObj.one_smul_self, ← LaxMonoidal.left_unitality]
  mul_smul := by
    change (LaxMonoidal.μ F G G ≫ F.map μ[G]) ▷ F.obj P ≫
        (LaxMonoidal.μ F G P ≫ F.map γ[G, P]) =
      (α_ (F.obj G) (F.obj G) (F.obj P)).hom ≫
        F.obj G ◁ (LaxMonoidal.μ F G P ≫ F.map γ[G, P]) ≫
          LaxMonoidal.μ F G P ≫ F.map γ[G, P]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.μ_natural_right_assoc]
    rw [← F.map_comp, ModObj.mul_smul_self, F.map_comp, F.map_comp]
    rw [LaxMonoidal.associativity_assoc]

/-- Applying the functor to points preserves the transported action. -/
theorem map_modObj_smul {T : C} (g : T ⟶ G) (p : T ⟶ P) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    F.map (g • p) = F.map g • F.map p := by
  intro transportedAction
  change F.map (lift g p ≫ γ[G, P]) =
    lift (F.map g) (F.map p) ≫ (LaxMonoidal.μ F G P ≫ F.map γ[G, P])
  rw [F.map_comp, ← Monoidal.lift_μ, Category.assoc]

/-- The transported torsor morphism is conjugate to the image of the
original torsor morphism by the actual product comparisons. -/
theorem leftSMul_modObjObj :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    ModObj.leftSMul (F.obj G) (F.obj P) =
      LaxMonoidal.μ F G P ≫ F.map (ModObj.leftSMul G P) ≫
        OplaxMonoidal.δ F P P := by
  intro transportedAction
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ModObj.leftSMul_fst, Category.assoc, OplaxMonoidal.δ_fst,
      ← F.map_comp]
    rfl
  · simp only [ModObj.leftSMul_snd, Category.assoc, OplaxMonoidal.δ_snd,
      ← F.map_comp, ModObj.leftSMul_snd, Monoidal.μ_snd]

/-- A monoidal functor preserves the actual simply transitive action.
In particular, scheme base change preserves a torsor's action isomorphism. -/
theorem isIso_leftSMul_modObjObj [IsIso (ModObj.leftSMul G P)] :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    IsIso (ModObj.leftSMul (F.obj G) (F.obj P)) := by
  intro transportedAction
  rw [F.leftSMul_modObjObj G P]
  infer_instance

/-- Transport preserves the actual difference between two torsor points. -/
theorem map_torsor_difference [IsIso (ModObj.leftSMul G P)]
    {T : C} (x y : T ⟶ P) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : IsIso (ModObj.leftSMul (F.obj G) (F.obj P)) :=
      F.isIso_leftSMul_modObjObj G P
    F.map (SchemeTheory.PointedTorsor.difference (G := G) x y) =
      SchemeTheory.PointedTorsor.difference (G := F.obj G) (F.map x) (F.map y) := by
  intro transportedAction transportedTorsor
  apply SchemeTheory.PointedTorsor.difference_unique
  rw [← F.map_modObj_smul G P, SchemeTheory.PointedTorsor.difference_smul]

/-- The coordinate morphism commutes with transport when its origin is
transported using the same monoidal unit comparison. -/
theorem map_torsor_coordinate [IsIso (ModObj.leftSMul G P)] (p : 𝟙_ C ⟶ P) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : IsIso (ModObj.leftSMul (F.obj G) (F.obj P)) :=
      F.isIso_leftSMul_modObjObj G P
    F.map (SchemeTheory.PointedTorsor.coordinate (G := G) p) =
      SchemeTheory.PointedTorsor.coordinate (G := F.obj G)
        (LaxMonoidal.ε F ≫ F.map p) := by
  intro transportedAction transportedTorsor
  have h := congrArg F.map
    (SchemeTheory.PointedTorsor.coordinate_smul (G := G) p (𝟙 P))
  have hs : F.map (SchemeTheory.PointedTorsor.coordinate (G := G) p) •
      (toUnit (F.obj P) ≫ (LaxMonoidal.ε F ≫ F.map p)) = 𝟙 (F.obj P) := by
    simpa only [Category.id_comp, F.map_modObj_smul, F.map_id, F.map_comp,
      ← Monoidal.toUnit_ε, Category.assoc] using h
  simpa only [Category.id_comp] using
    SchemeTheory.PointedTorsor.coordinate_unique
      (LaxMonoidal.ε F ≫ F.map p) (𝟙 (F.obj P))
      (F.map (SchemeTheory.PointedTorsor.coordinate (G := G) p)) hs


/-- A natural transformation between Cartesian monoidal functors intertwines
their transported actions on every test object. This applies to the native
composition comparison for successive pullbacks. -/
theorem natTrans_modObj_smul (F' : C ⥤ D) [F'.Monoidal] (τ : F ⟶ F')
    {T : D} (g : T ⟶ F.obj G) (p : T ⟶ F.obj P) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : ModObj (F'.obj G) (F'.obj P) := F'.modObjObj G P
    (g • p) ≫ τ.app P = (g ≫ τ.app G) • (p ≫ τ.app P) := by
  intro sourceAction targetAction
  change (lift g p ≫ (LaxMonoidal.μ F G P ≫ F.map γ[G, P])) ≫ τ.app P =
    lift (g ≫ τ.app G) (p ≫ τ.app P) ≫
      (LaxMonoidal.μ F' G P ≫ F'.map γ[G, P])
  have ht : LaxMonoidal.μ F G P ≫ τ.app (MonoidalLeftActionStruct.actionObj G P) =
      (τ.app G ⊗ₘ τ.app P) ≫ LaxMonoidal.μ F' G P :=
    NatTrans.IsMonoidal.tensor (τ := τ) G P
  rw [Category.assoc, Category.assoc, τ.naturality γ[G, P],
    ← Category.assoc (LaxMonoidal.μ F G P), ht, Category.assoc,
    ← Category.assoc (lift g p), ← lift_map]


/-- The native composition comparison also intertwines successive
transported actions. The two transports retain their own canonical
monoid structures; only their actual action morphisms are compared. -/
theorem natTrans_comp_modObj_smul
    {E : Type*} [Category E] [CartesianMonoidalCategory E]
    (F₁ : C ⥤ E) [F₁.Monoidal] (F₂ : E ⥤ D) [F₂.Monoidal]
    (τ : F ⟶ F₁ ⋙ F₂) {T : D} (g : T ⟶ F.obj G) (p : T ⟶ F.obj P) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : ModObj (F₁.obj G) (F₁.obj P) := F₁.modObjObj G P
    let _ : ModObj (F₂.obj (F₁.obj G)) (F₂.obj (F₁.obj P)) :=
      F₂.modObjObj (F₁.obj G) (F₁.obj P)
    (g • p) ≫ τ.app P =
      (show T ⟶ F₂.obj (F₁.obj G) from g ≫ τ.app G) •
        (show T ⟶ F₂.obj (F₁.obj P) from p ≫ τ.app P) := by
  intro sourceAction intermediateAction targetAction
  change (lift g p ≫ (LaxMonoidal.μ F G P ≫ F.map γ[G, P])) ≫ τ.app P =
    lift (g ≫ τ.app G) (p ≫ τ.app P) ≫
      (LaxMonoidal.μ F₂ (F₁.obj G) (F₁.obj P) ≫
        F₂.map (LaxMonoidal.μ F₁ G P ≫ F₁.map γ[G, P]))
  rw [F₂.map_comp, ← Category.assoc (LaxMonoidal.μ F₂ (F₁.obj G) (F₁.obj P))]
  exact F.natTrans_modObj_smul G P (F₁ ⋙ F₂) τ g p

/-- The same natural comparison preserves the actual difference of two
torsor points, using the transported simply transitive actions. -/
theorem natTrans_torsor_difference [IsIso (ModObj.leftSMul G P)]
    (F' : C ⥤ D) [F'.Monoidal] (τ : F ⟶ F')
    {T : D} (x y : T ⟶ F.obj P) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : ModObj (F'.obj G) (F'.obj P) := F'.modObjObj G P
    let _ : IsIso (ModObj.leftSMul (F.obj G) (F.obj P)) :=
      F.isIso_leftSMul_modObjObj G P
    let _ : IsIso (ModObj.leftSMul (F'.obj G) (F'.obj P)) :=
      F'.isIso_leftSMul_modObjObj G P
    SchemeTheory.PointedTorsor.difference (G := F.obj G) x y ≫ τ.app G =
      SchemeTheory.PointedTorsor.difference (G := F'.obj G)
        (x ≫ τ.app P) (y ≫ τ.app P) := by
  intro sourceAction targetAction sourceTorsor targetTorsor
  apply SchemeTheory.PointedTorsor.difference_unique
  rw [← F.natTrans_modObj_smul G P F' τ,
    SchemeTheory.PointedTorsor.difference_smul]

/-- Coordinates based at any point of the transported torsor commute with
the natural comparison. The origin need not descend through either functor. -/
theorem natTrans_torsor_coordinate [IsIso (ModObj.leftSMul G P)]
    (F' : C ⥤ D) [F'.Monoidal] (τ : F ⟶ F')
    (p : 𝟙_ D ⟶ F.obj P) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : ModObj (F'.obj G) (F'.obj P) := F'.modObjObj G P
    let _ : IsIso (ModObj.leftSMul (F.obj G) (F.obj P)) :=
      F.isIso_leftSMul_modObjObj G P
    let _ : IsIso (ModObj.leftSMul (F'.obj G) (F'.obj P)) :=
      F'.isIso_leftSMul_modObjObj G P
    SchemeTheory.PointedTorsor.coordinate (G := F.obj G) p ≫ τ.app G =
      τ.app P ≫ SchemeTheory.PointedTorsor.coordinate (G := F'.obj G)
        (p ≫ τ.app P) := by
  intro sourceAction targetAction sourceTorsor targetTorsor
  apply SchemeTheory.PointedTorsor.coordinate_unique
  have h := congrArg (fun a => a ≫ τ.app P)
    (SchemeTheory.PointedTorsor.coordinate_smul (G := F.obj G) p (𝟙 (F.obj P)))
  rw [F.natTrans_modObj_smul G P F' τ] at h
  simpa only [Category.id_comp, Category.assoc] using h

end CategoryTheory.Functor
