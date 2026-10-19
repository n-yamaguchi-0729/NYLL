/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates

/-! # Equivariant morphisms from actual pointed torsors -/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchemeTheory.PointedTorsor

variable {B : Type u} [Category.{v} B] [CartesianMonoidalCategory B]
  {G P H Q : B} [MonObj G] [ModObj G P] [IsIso (ModObj.leftSMul G P)]
  [MonObj H] [ModObj H Q]

/-- An actual homomorphism and two actual points give an actual equivariant morphism. -/
def map (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P) (q : 𝟙_ B ⟶ Q) : P ⟶ Q :=
  (coordinate p ≫ φ) • (toUnit P ≫ q)

/-- Evaluation is translation by the image of the actual coordinate. -/
theorem map_apply (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P) (q : 𝟙_ B ⟶ Q)
    {T : B} (x : T ⟶ P) :
    x ≫ map φ p q = ((x ≫ coordinate p) ≫ φ) • (toUnit T ≫ q) := by
  simp only [map, ModObj.comp_smul, Category.assoc, comp_toUnit_assoc]

/-- The constructed morphism has the prescribed value at the source point. -/
theorem map_basepoint (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P)
    (q : 𝟙_ B ⟶ Q) : p ≫ map φ p q = q := by
  have hp : p ≫ coordinate (G := G) p = 1 := by
    simpa only [toUnit_unit, Category.id_comp] using coordinate_basepoint (G := G) p (𝟙_ B)
  rw [map_apply, hp, MonObj.one_comp, one_smul, toUnit_unit, Category.id_comp]

/-- The morphism respects the actual actions on every test object. -/
theorem map_equivariant (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P)
    (q : 𝟙_ B ⟶ Q) {T : B} (g : T ⟶ G) (x : T ⟶ P) :
    (g • x) ≫ map φ p q = (g ≫ φ) • (x ≫ map φ p q) := by
  rw [map_apply, coordinate_smul_eq, MonObj.mul_comp, mul_smul, map_apply]

/-- Equivariance is an equality of the actual action morphisms. -/
theorem map_action_square (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P)
    (q : 𝟙_ B ⟶ Q) :
    γ[G, P] ≫ map φ p q = (φ ⊗ₘ map φ p q) ≫ γ[H, Q] := by
  have h := map_equivariant φ p q (fst G P) (snd G P)
  simpa only [CategoryTheory.Hom.smul_def, ← lift_map, lift_fst_snd,
    Category.id_comp] using h

/-- The constructed morphism is a standard module-object morphism after scalar restriction. -/
theorem map_isModHom (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P)
    (q : 𝟙_ B ⟶ Q) :
    let _ : ModObj G Q := Mod.scalarRestriction φ Q
    IsModHom G (map φ p q) := by
  intro restrictedAction
  constructor
  change γ[G, P] ≫ map φ p q = G ◁ map φ p q ≫ (φ ▷ Q ≫ γ[H, Q])
  rw [← Category.assoc, ← tensorHom_def']
  exact map_action_square φ p q

/-- A point value determines an equivariant morphism from an actual pointed torsor. -/
theorem map_unique (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P)
    (q : 𝟙_ B ⟶ Q) (f : P ⟶ Q) (hp : p ≫ f = q)
    (hf : ∀ (T : B) (g : T ⟶ G) (x : T ⟶ P),
      (g • x) ≫ f = (g ≫ φ) • (x ≫ f)) :
    f = map φ p q := by
  have hc : coordinate (G := G) p • (toUnit P ≫ p) = 𝟙 P := by
    simpa only [Category.id_comp] using coordinate_smul (G := G) p (𝟙 P)
  calc
    f = (coordinate p • (toUnit P ≫ p)) ≫ f := by rw [hc, Category.id_comp]
    _ = (coordinate p ≫ φ) • ((toUnit P ≫ p) ≫ f) := hf P _ _
    _ = map φ p q := by rw [Category.assoc, hp]; rfl

/-- Existence and uniqueness concern actual morphisms, without a representability assumption. -/
theorem existsUnique_map (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P)
    (q : 𝟙_ B ⟶ Q) :
    ∃! (f : P ⟶ Q), p ≫ f = q ∧
      ∀ (T : B) (g : T ⟶ G) (x : T ⟶ P),
        (g • x) ≫ f = (g ≫ φ) • (x ≫ f) := by
  refine ⟨map φ p q, ⟨map_basepoint φ p q, fun _ g x => map_equivariant φ p q g x⟩, ?_⟩
  intro f hf
  exact map_unique φ p q f hf.1 hf.2

/-- Changing the chosen origins to corresponding actual points preserves the morphism. -/
theorem map_changeBasepoint (φ : G ⟶ H) [IsMonHom φ]
    (p p' : 𝟙_ B ⟶ P) (q : 𝟙_ B ⟶ Q) :
    map φ p' (p' ≫ map φ p q) = map φ p q :=
  (map_unique φ p' _ (map φ p q) rfl (fun _ g x => map_equivariant φ p q g x)).symm

/-- Between actual pointed torsors, the morphism is the homomorphism in actual coordinates. -/
theorem map_eq_trivializations [IsIso (ModObj.leftSMul H Q)]
    (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P) (q : 𝟙_ B ⟶ Q) :
    map φ p q = (trivialization p).hom ≫ φ ≫ (trivialization q).inv := by
  change (coordinate p ≫ φ) • (toUnit P ≫ q) =
    coordinate p ≫ φ ≫ ((𝟙 H) • (toUnit H ≫ q))
  rw [← Category.assoc, ModObj.comp_smul, Category.comp_id, comp_toUnit_assoc]

/-- Taking target coordinates recovers the actual homomorphism of source coordinates. -/
theorem map_coordinate [IsIso (ModObj.leftSMul H Q)]
    (φ : G ⟶ H) [IsMonHom φ] (p : 𝟙_ B ⟶ P) (q : 𝟙_ B ⟶ Q) :
    map φ p q ≫ coordinate q = coordinate p ≫ φ := by
  change map φ p q ≫ (trivialization q).hom = (trivialization p).hom ≫ φ
  rw [map_eq_trivializations, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end SchemeTheory.PointedTorsor


namespace CategoryTheory.Functor

open scoped CategoryTheory.Obj

universe u' v'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]
  {G P H Q : C} [MonObj G] [ModObj G P] [IsIso (ModObj.leftSMul G P)]
  [MonObj H] [ModObj H Q]

omit [IsIso (ModObj.leftSMul G P)] in
/-- Monoidal transport preserves equivariance on all target-category test
objects, not only those in the image of the functor. -/
theorem map_modObj_equivariant (φ : G ⟶ H) (f : P ⟶ Q)
    (hf : ∀ (T : C) (g : T ⟶ G) (x : T ⟶ P),
      (g • x) ≫ f = (g ≫ φ) • (x ≫ f)) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : ModObj (F.obj H) (F.obj Q) := F.modObjObj H Q
    ∀ (T : D) (g : T ⟶ F.obj G) (x : T ⟶ F.obj P),
      (g • x) ≫ F.map f = (g ≫ F.map φ) • (x ≫ F.map f) := by
  intro sourceAction targetAction T g x
  have hs : γ[G, P] ≫ f = (φ ⊗ₘ f) ≫ γ[H, Q] := by
    have h := hf (G ⊗ P) (fst G P) (snd G P)
    simpa only [CategoryTheory.Hom.smul_def, ← lift_map, lift_fst_snd,
      Category.id_comp] using h
  change (lift g x ≫ (LaxMonoidal.μ F G P ≫ F.map γ[G, P])) ≫ F.map f =
    lift (g ≫ F.map φ) (x ≫ F.map f) ≫ (LaxMonoidal.μ F H Q ≫ F.map γ[H, Q])
  rw [Category.assoc, Category.assoc, ← F.map_comp, hs, F.map_comp]
  rw [← LaxMonoidal.μ_natural_assoc, ← lift_map, Category.assoc]

/-- The actual equivariant map constructed from origins commutes with a
monoidal functor, using its unit comparison for both origins. -/
theorem map_pointedTorsorMap (φ : G ⟶ H) [IsMonHom φ]
    (p : 𝟙_ C ⟶ P) (q : 𝟙_ C ⟶ Q) :
    let _ : ModObj (F.obj G) (F.obj P) := F.modObjObj G P
    let _ : IsIso (ModObj.leftSMul (F.obj G) (F.obj P)) :=
      F.isIso_leftSMul_modObjObj G P
    let _ : ModObj (F.obj H) (F.obj Q) := F.modObjObj H Q
    F.map (SchemeTheory.PointedTorsor.map φ p q) =
      SchemeTheory.PointedTorsor.map (F.map φ)
        (LaxMonoidal.ε F ≫ F.map p) (LaxMonoidal.ε F ≫ F.map q) := by
  intro sourceAction sourceTorsor targetAction
  change F.map ((SchemeTheory.PointedTorsor.coordinate p ≫ φ) • (toUnit P ≫ q)) =
    (SchemeTheory.PointedTorsor.coordinate (LaxMonoidal.ε F ≫ F.map p) ≫ F.map φ) •
      (toUnit (F.obj P) ≫ (LaxMonoidal.ε F ≫ F.map q))
  rw [F.map_modObj_smul H Q, F.map_comp, F.map_torsor_coordinate,
    F.map_comp, ← Monoidal.toUnit_ε, Category.assoc]

end CategoryTheory.Functor
