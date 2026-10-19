/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparison
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-! # Equivariant comparisons along a monoidal functor tower

Successive group and action comparisons give the actual composite group
comparison and its equivariance. The namespace is retained for existing users.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace AlgebraicGeometry.GeneralizedJacobian

/-- An inverse isomorphism preserves the supplied action compatibility. -/
private theorem equivariant_inverse_apply
    {B : Type u} [Category.{v} B] [CartesianMonoidalCategory B]
    {G H P Q : B} [MonObj G] [ModObj G P] [MonObj H] [ModObj H Q]
    (φ : G ⟶ H) (ψ : H ⟶ G) (e : P ≅ Q) (hψφ : ψ ≫ φ = 𝟙 H)
    (hf : ∀ (T : B) (g : T ⟶ G) (p : T ⟶ P),
      (g • p) ≫ e.hom = (g ≫ φ) • (p ≫ e.hom))
    {T : B} (g : T ⟶ H) (p : T ⟶ Q) :
    (g • p) ≫ e.inv = (g ≫ ψ) • (p ≫ e.inv) := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, e.inv_hom_id, Category.comp_id, hf,
    Category.assoc, hψφ, Category.comp_id, Category.assoc,
    e.inv_hom_id, Category.comp_id]

/-- Successive equivariant maps and the native composition comparison
preserve the action before any represented group schemes are substituted. -/
private theorem equivariant_monoidal_tower_apply
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C]
    (F : A ⥤ C) [F.Monoidal]
    (F₁ : A ⥤ B) [F₁.Monoidal] (F₂ : B ⥤ C) [F₂.Monoidal]
    (e : F ≅ F₁ ⋙ F₂)
    (G₀ P₀ : A) [MonObj G₀] [ModObj G₀ P₀]
    (G₁ P₁ : B) [MonObj G₁] [ModObj G₁ P₁]
    (G₂ P₂ G₃ P₃ : C) [MonObj G₂] [ModObj G₂ P₂]
    [MonObj G₃] [ModObj G₃ P₃]
    (bcomp : F₂.obj (F₁.obj G₀) ⟶ F.obj G₀) (hbcomp : bcomp = e.inv.app G₀)
    (b₁ : G₁ ⟶ F₁.obj G₀) (p₁ : P₁ ⟶ F₁.obj P₀)
    (b₂ : G₂ ⟶ F₂.obj G₁) (p₂ : P₂ ⟶ F₂.obj P₁)
    (b₀ : F.obj G₀ ⟶ G₃) (p₀ : F.obj P₀ ⟶ P₃) :
    let _mod₁ : ModObj (F₁.obj G₀) (F₁.obj P₀) := F₁.modObjObj G₀ P₀
    let _mod₂ : ModObj (F₂.obj G₁) (F₂.obj P₁) := F₂.modObjObj G₁ P₁
    let _mod₁₂ : ModObj (F₂.obj (F₁.obj G₀)) (F₂.obj (F₁.obj P₀)) :=
      F₂.modObjObj (F₁.obj G₀) (F₁.obj P₀)
    let _mod₀ : ModObj (F.obj G₀) (F.obj P₀) := F.modObjObj G₀ P₀
    ∀ (_h₁ : ∀ (T : B) (g : T ⟶ G₁) (x : T ⟶ P₁),
        (g • x) ≫ p₁ = (g ≫ b₁) • (x ≫ p₁))
      (_h₂ : ∀ (T : C) (g : T ⟶ G₂) (x : T ⟶ P₂),
        (g • x) ≫ p₂ = (g ≫ b₂) • (x ≫ p₂))
      (_h₀ : ∀ (T : C) (g : T ⟶ F.obj G₀) (x : T ⟶ F.obj P₀),
        (g • x) ≫ p₀ = (g ≫ b₀) • (x ≫ p₀))
      (T : C) (g : T ⟶ G₂) (x : T ⟶ P₂),
      (g • x) ≫ (p₂ ≫ F₂.map p₁ ≫ e.inv.app P₀ ≫ p₀) =
        (g ≫ (b₂ ≫ F₂.map b₁ ≫ bcomp ≫ b₀)) •
          (x ≫ (p₂ ≫ F₂.map p₁ ≫ e.inv.app P₀ ≫ p₀)) := by
  intro mod₁ mod₂ mod₁₂ mod₀ h₁ h₂ h₀ T g x
  have hsecond (a : T ⟶ F₂.obj G₁) (p : T ⟶ F₂.obj P₁) :
      (a • p) ≫ F₂.map p₁ = (a ≫ F₂.map b₁) • (p ≫ F₂.map p₁) :=
    @Functor.map_modObj_equivariant B _ _ C _ _ F₂ _
      G₁ P₁ (F₁.obj G₀) (F₁.obj P₀) _ _ _ mod₁ b₁ p₁ h₁ T a p
  have hcomp (a : T ⟶ F₂.obj (F₁.obj G₀))
      (p : T ⟶ F₂.obj (F₁.obj P₀)) :
      (a • p) ≫ e.inv.app P₀ =
        (a ≫ e.inv.app G₀) • (p ≫ e.inv.app P₀) := by
    exact @equivariant_inverse_apply C _ _
      (F.obj G₀) (F₂.obj (F₁.obj G₀))
      (F.obj P₀) (F₂.obj (F₁.obj P₀))
      _ mod₀ _ mod₁₂ (e.hom.app G₀) (e.inv.app G₀) (e.app P₀)
      (Iso.inv_hom_id_app e G₀)
      (fun _ a p => F.natTrans_comp_modObj_smul G₀ P₀ F₁ F₂ e.hom a p) T a p
  rw [hbcomp]
  simp only [← Category.assoc]
  exact (congrArg (fun p => ((p ≫ F₂.map p₁) ≫ e.inv.app P₀) ≫ p₀)
    (h₂ T g x)).trans
      ((congrArg (fun p => (p ≫ e.inv.app P₀) ≫ p₀)
        (hsecond (g ≫ b₂) (x ≫ p₂))).trans
          ((congrArg (fun p => p ≫ p₀)
            (hcomp ((g ≫ b₂) ≫ F₂.map b₁) ((x ≫ p₂) ≫ F₂.map p₁))).trans
              (h₀ T (((g ≫ b₂) ≫ F₂.map b₁) ≫ e.inv.app G₀)
                (((x ≫ p₂) ≫ F₂.map p₁) ≫ e.inv.app P₀))))

/-- The underlying action compatibility of a tower of commutative group
objects is calculated before specializing their represented group laws. -/
theorem equivariant_commGrp_tower_apply
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (F : A ⥤ C) [F.Braided]
    (F₁ : A ⥤ B) [F₁.Braided] (F₂ : B ⥤ C) [F₂.Braided]
    (e : F ≅ F₁ ⋙ F₂)
    (G₀ : CommGrp A) (P₀ : A) [ModObj G₀.X P₀]
    (G₁ : CommGrp B) (P₁ : B) [ModObj G₁.X P₁]
    (G₂ G₃ : CommGrp C) (P₂ P₃ : C) [ModObj G₂.X P₂] [ModObj G₃.X P₃]
    (b₁ : G₁ ≅ F₁.mapCommGrp.obj G₀) (p₁ : P₁ ≅ F₁.obj P₀)
    (b₂ : G₂ ≅ F₂.mapCommGrp.obj G₁) (p₂ : P₂ ≅ F₂.obj P₁)
    (b₀ : F.mapCommGrp.obj G₀ ≅ G₃) (p₀ : F.obj P₀ ≅ P₃) :
    let _mod₁ : ModObj (F₁.obj G₀.X) (F₁.obj P₀) := F₁.modObjObj G₀.X P₀
    let _mod₂ : ModObj (F₂.obj G₁.X) (F₂.obj P₁) := F₂.modObjObj G₁.X P₁
    let _mod₀ : ModObj (F.obj G₀.X) (F.obj P₀) := F.modObjObj G₀.X P₀
    ∀ (_h₁ : ∀ (T : B) (g : T ⟶ G₁.X) (x : T ⟶ P₁),
        (g • x) ≫ p₁.hom = (g ≫ (show G₁.X ⟶ F₁.obj G₀.X from b₁.hom.hom.hom.hom)) • (x ≫ p₁.hom))
      (_h₂ : ∀ (T : C) (g : T ⟶ G₂.X) (x : T ⟶ P₂),
        (g • x) ≫ p₂.hom = (g ≫ (show G₂.X ⟶ F₂.obj G₁.X from b₂.hom.hom.hom.hom)) • (x ≫ p₂.hom))
      (_h₀ : ∀ (T : C) (g : T ⟶ F.obj G₀.X) (x : T ⟶ F.obj P₀),
        (g • x) ≫ p₀.hom = (g ≫ b₀.hom.hom.hom.hom) • (x ≫ p₀.hom)),
    let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    let eG := b₂ ≪≫ F₂.mapCommGrp.mapIso b₁ ≪≫ (eB.app G₀).symm ≪≫ b₀
    let eP := p₂ ≪≫ F₂.mapIso p₁ ≪≫ (e.app P₀).symm ≪≫ p₀
    ∀ (T : C) (g : T ⟶ G₂.X) (x : T ⟶ P₂),
      (g • x) ≫ eP.hom = (g ≫ eG.hom.hom.hom.hom) • (x ≫ eP.hom) := by
  intro mod₁ mod₂ mod₀ h₁ h₂ h₀ eB eG eP T g x
  have heB : (eB.app G₀).inv.hom.hom.hom = e.inv.app G₀.X := by
    change 𝟙 _ ≫ e.inv.app G₀.X = e.inv.app G₀.X
    exact Category.id_comp _
  exact equivariant_monoidal_tower_apply F F₁ F₂ e G₀.X P₀ G₁.X P₁
    G₂.X P₂ G₃.X P₃ (eB.app G₀).inv.hom.hom.hom heB
    b₁.hom.hom.hom.hom p₁.hom b₂.hom.hom.hom.hom p₂.hom
    b₀.hom.hom.hom.hom p₀.hom h₁ h₂ h₀ T g x

theorem equivariant_commGrp_tower_comparison_apply
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (F : A ⥤ C) [F.Braided]
    (F₁ : A ⥤ B) [F₁.Braided] (F₂ : B ⥤ C) [F₂.Braided]
    (e : F ≅ F₁ ⋙ F₂)
    (G₀ : CommGrp A) (P₀ : A) [ModObj G₀.X P₀]
    (G₁ : CommGrp B) (P₁ : B) [ModObj G₁.X P₁]
    (G₂ G₃ : CommGrp C) (P₂ P₃ : C) [ModObj G₂.X P₂] [ModObj G₃.X P₃]
    (b₁ : G₁ ≅ F₁.mapCommGrp.obj G₀) (p₁ : P₁ ≅ F₁.obj P₀)
    (b₂ : G₂ ≅ F₂.mapCommGrp.obj G₁) (p₂ : P₂ ≅ F₂.obj P₁)
    (b₀ : F.mapCommGrp.obj G₀ ≅ G₃) (p₀ : F.obj P₀ ≅ P₃) :
    let _mod₁ : ModObj (F₁.obj G₀.X) (F₁.obj P₀) := F₁.modObjObj G₀.X P₀
    let _mod₂ : ModObj (F₂.obj G₁.X) (F₂.obj P₁) := F₂.modObjObj G₁.X P₁
    let _mod₀ : ModObj (F.obj G₀.X) (F.obj P₀) := F.modObjObj G₀.X P₀
    ∀ (_h₁ : ∀ (T : B) (g : T ⟶ G₁.X) (x : T ⟶ P₁),
        (g • x) ≫ p₁.hom = (g ≫ (show G₁.X ⟶ F₁.obj G₀.X from b₁.hom.hom.hom.hom)) • (x ≫ p₁.hom))
      (_h₂ : ∀ (T : C) (g : T ⟶ G₂.X) (x : T ⟶ P₂),
        (g • x) ≫ p₂.hom = (g ≫ (show G₂.X ⟶ F₂.obj G₁.X from b₂.hom.hom.hom.hom)) • (x ≫ p₂.hom))
      (_h₀ : ∀ (T : C) (g : T ⟶ F.obj G₀.X) (x : T ⟶ F.obj P₀),
        (g • x) ≫ p₀.hom = (g ≫ b₀.hom.hom.hom.hom) • (x ≫ p₀.hom)),
    let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    let eG := scalarTowerComparisonIso F.mapCommGrp F₁.mapCommGrp F₂.mapCommGrp
      eB b₁ b₂ b₀
    let eP := scalarTowerComparisonIso F F₁ F₂ e p₁ p₂ p₀
    ∀ (T : C) (g : T ⟶ G₂.X) (x : T ⟶ P₂),
      (g • x) ≫ eP.hom = (g ≫ eG.hom.hom.hom.hom) • (x ≫ eP.hom) := by
  intro mod₁ mod₂ mod₀ h₁ h₂ h₀ eB eG eP T g x
  have heB : (eB.app G₀).inv.hom.hom.hom = e.inv.app G₀.X := by
    change 𝟙 _ ≫ e.inv.app G₀.X = e.inv.app G₀.X
    exact Category.id_comp _
  exact equivariant_monoidal_tower_apply F F₁ F₂ e G₀.X P₀ G₁.X P₁
    G₂.X P₂ G₃.X P₃ (eB.app G₀).inv.hom.hom.hom heB
    b₁.hom.hom.hom.hom p₁.hom b₂.hom.hom.hom.hom p₂.hom
    b₀.hom.hom.hom.hom p₀.hom h₁ h₂ h₀ T g x

theorem exists_equivariant_commGrp_tower_comparison
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (F : A ⥤ C) [F.Braided]
    (F₁ : A ⥤ B) [F₁.Braided] (F₂ : B ⥤ C) [F₂.Braided]
    (e : F ≅ F₁ ⋙ F₂)
    (G₀ : CommGrp A) (P₀ : A) [ModObj G₀.X P₀]
    (G₁ : CommGrp B) (P₁ : B) [ModObj G₁.X P₁]
    (G₂ G₃ : CommGrp C) (P₂ P₃ : C) [ModObj G₂.X P₂] [ModObj G₃.X P₃]
    (b₁ : G₁ ≅ F₁.mapCommGrp.obj G₀) (p₁ : P₁ ≅ F₁.obj P₀)
    (b₂ : G₂ ≅ F₂.mapCommGrp.obj G₁) (p₂ : P₂ ≅ F₂.obj P₁)
    (b₀ : F.mapCommGrp.obj G₀ ≅ G₃) (p₀ : F.obj P₀ ≅ P₃) :
    let _mod₁ : ModObj (F₁.obj G₀.X) (F₁.obj P₀) := F₁.modObjObj G₀.X P₀
    let _mod₂ : ModObj (F₂.obj G₁.X) (F₂.obj P₁) := F₂.modObjObj G₁.X P₁
    let _mod₀ : ModObj (F.obj G₀.X) (F.obj P₀) := F.modObjObj G₀.X P₀
    ∀ (_h₁ : ∀ (T : B) (g : T ⟶ G₁.X) (x : T ⟶ P₁),
        (g • x) ≫ p₁.hom = (g ≫ (show G₁.X ⟶ F₁.obj G₀.X from b₁.hom.hom.hom.hom)) • (x ≫ p₁.hom))
      (_h₂ : ∀ (T : C) (g : T ⟶ G₂.X) (x : T ⟶ P₂),
        (g • x) ≫ p₂.hom = (g ≫ (show G₂.X ⟶ F₂.obj G₁.X from b₂.hom.hom.hom.hom)) • (x ≫ p₂.hom))
      (_h₀ : ∀ (T : C) (g : T ⟶ F.obj G₀.X) (x : T ⟶ F.obj P₀),
        (g • x) ≫ p₀.hom = (g ≫ b₀.hom.hom.hom.hom) • (x ≫ p₀.hom)),
    let eP := scalarTowerComparisonIso F F₁ F₂ e p₁ p₂ p₀
    ∃ eG : G₂ ≅ G₃, ∀ (T : C) (g : T ⟶ G₂.X) (x : T ⟶ P₂),
      (g • x) ≫ eP.hom = (g ≫ eG.hom.hom.hom.hom) • (x ≫ eP.hom) := by
  intro mod₁ mod₂ mod₀ h₁ h₂ h₀ eP
  refine ⟨scalarTowerComparisonIso F.mapCommGrp F₁.mapCommGrp F₂.mapCommGrp
    (Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso) b₁ b₂ b₀, ?_⟩
  exact equivariant_commGrp_tower_comparison_apply F F₁ F₂ e
    G₀ P₀ G₁ P₁ G₂ G₃ P₂ P₃ b₁ p₁ b₂ p₂ b₀ p₀ h₁ h₂ h₀

/-- An equivariant map and a further equivariant transport preserve the action
after a monoidal tower comparison. The comparison and the two maps are composed
before any particular represented group or torsor is substituted. -/
theorem equivariant_commGrp_tower_comp_apply
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (F : A ⥤ C) [F.Braided]
    (F₁ : A ⥤ B) [F₁.Braided] (F₂ : B ⥤ C) [F₂.Braided]
    (e : F ≅ F₁ ⋙ F₂)
    (G₀ : CommGrp A) (P₀ : A) [ModObj G₀.X P₀]
    (G₁ : CommGrp B) (P₁ : B) [ModObj G₁.X P₁]
    (G₂ G₃ H₀ H₁ : CommGrp C) (P₂ P₃ Q₀ Q₁ : C)
    [ModObj G₂.X P₂] [ModObj G₃.X P₃] [ModObj H₀.X Q₀] [ModObj H₁.X Q₁]
    (b₁ : G₁ ≅ F₁.mapCommGrp.obj G₀) (p₁ : P₁ ≅ F₁.obj P₀)
    (b₂ : G₂ ≅ F₂.mapCommGrp.obj G₁) (p₂ : P₂ ≅ F₂.obj P₁)
    (b₀ : F.mapCommGrp.obj G₀ ≅ G₃) (p₀ : F.obj P₀ ≅ P₃)
    (φ : G₃ ⟶ H₀) (τ : H₀ ⟶ H₁) (f : P₃ ⟶ Q₀) (q : Q₀ ⟶ Q₁)
    (hf : ∀ (T : C) (a : T ⟶ G₃.X) (x : T ⟶ P₃),
      (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f))
    (hq : ∀ (T : C) (a : T ⟶ H₀.X) (x : T ⟶ Q₀),
      (a • x) ≫ q = (a ≫ τ.hom.hom.hom) • (x ≫ q)) :
    let _mod₁ : ModObj (F₁.obj G₀.X) (F₁.obj P₀) := F₁.modObjObj G₀.X P₀
    let _mod₂ : ModObj (F₂.obj G₁.X) (F₂.obj P₁) := F₂.modObjObj G₁.X P₁
    let _mod₀ : ModObj (F.obj G₀.X) (F.obj P₀) := F.modObjObj G₀.X P₀
    ∀ (_h₁ : ∀ (T : B) (g : T ⟶ G₁.X) (x : T ⟶ P₁),
        (g • x) ≫ p₁.hom =
          (g ≫ (show G₁.X ⟶ F₁.obj G₀.X from b₁.hom.hom.hom.hom)) • (x ≫ p₁.hom))
      (_h₂ : ∀ (T : C) (g : T ⟶ G₂.X) (x : T ⟶ P₂),
        (g • x) ≫ p₂.hom =
          (g ≫ (show G₂.X ⟶ F₂.obj G₁.X from b₂.hom.hom.hom.hom)) • (x ≫ p₂.hom))
      (_h₀ : ∀ (T : C) (g : T ⟶ F.obj G₀.X) (x : T ⟶ F.obj P₀),
        (g • x) ≫ p₀.hom = (g ≫ b₀.hom.hom.hom.hom) • (x ≫ p₀.hom)),
    let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    let eG := b₂ ≪≫ F₂.mapCommGrp.mapIso b₁ ≪≫ (eB.app G₀).symm ≪≫ b₀
    let eP := p₂ ≪≫ F₂.mapIso p₁ ≪≫ (e.app P₀).symm ≪≫ p₀
    ∀ (T : C) (a : T ⟶ G₂.X) (x : T ⟶ P₂),
      (a • x) ≫ (eP.hom ≫ f ≫ q) =
        (a ≫ (eG.hom ≫ φ ≫ τ).hom.hom.hom) • (x ≫ (eP.hom ≫ f ≫ q)) := by
  intro mod₁ mod₂ mod₀ h₁ h₂ h₀ eB eG eP T a x
  have hfirst := equivariant_commGrp_tower_apply F F₁ F₂ e
    G₀ P₀ G₁ P₁ G₂ G₃ P₂ P₃ b₁ p₁ b₂ p₂ b₀ p₀ h₁ h₂ h₀ T a x
  have hsecond := hf T (a ≫ eG.hom.hom.hom.hom) (x ≫ eP.hom)
  have hthird := hq T ((a ≫ eG.hom.hom.hom.hom) ≫ φ.hom.hom.hom)
    ((x ≫ eP.hom) ≫ f)
  change (a • x) ≫ (eP.hom ≫ f ≫ q) =
    (a ≫ (eG.hom.hom.hom.hom ≫ φ.hom.hom.hom ≫ τ.hom.hom.hom)) •
      (x ≫ (eP.hom ≫ f ≫ q))
  have ha :
      ((a ≫ eG.hom.hom.hom.hom) ≫ φ.hom.hom.hom) ≫ τ.hom.hom.hom =
        a ≫ (eG.hom.hom.hom.hom ≫ φ.hom.hom.hom ≫ τ.hom.hom.hom) :=
    (Category.assoc (a ≫ eG.hom.hom.hom.hom) φ.hom.hom.hom τ.hom.hom.hom).trans
      (Category.assoc a eG.hom.hom.hom.hom (φ.hom.hom.hom ≫ τ.hom.hom.hom))
  have hx : ((x ≫ eP.hom) ≫ f) ≫ q = x ≫ (eP.hom ≫ f ≫ q) :=
    (Category.assoc (x ≫ eP.hom) f q).trans (Category.assoc x eP.hom (f ≫ q))
  have hsource : (a • x) ≫ (eP.hom ≫ f ≫ q) =
      (((a • x) ≫ eP.hom) ≫ f) ≫ q :=
    ((Category.assoc ((a • x) ≫ eP.hom) f q).trans
      (Category.assoc (a • x) eP.hom (f ≫ q))).symm
  have htarget := congrArg₂ (fun (a' : T ⟶ H₁.X) (x' : T ⟶ Q₁) => a' • x') ha hx
  exact hsource.trans
    ((congrArg (fun z => (z ≫ f) ≫ q) hfirst).trans
      ((congrArg (fun z => z ≫ q) hsecond).trans (hthird.trans htarget)))

end AlgebraicGeometry.GeneralizedJacobian
