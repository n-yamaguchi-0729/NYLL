/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Mathlib.CategoryTheory.Adjunction.Mates
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorUnitObjIsoHomAppPullbackLocalSectionUnitSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.PullbackCompHomAppCompPullbackUnitIsoHom
import Nyll.SchemeTheory.Modules.Functoriality.PullbackCompPullbackCongrPasteSquaresApp

/-!
# Composition of pullbacks of chosen rigidifications

The comparison preserves the actual trivializations. This is stronger than identifying the
underlying line bundles, and supplies the composition law for the maps on naive classes.
-/

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

open AlgebraicCurves.Geometry.Sheaves.Proofs
open PullbackUnitComposition.AlgebraicGeometry.Scheme.Modules
open Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
open AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

/-- The unit comparison defined by adjunction equals the monoidal unit comparison. -/
theorem pullbackUnitComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pullbackUnitIso f = Scheme.Modules.pullbackTensorUnitObjIso f := by
  apply CategoryTheory.Iso.ext
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  calc
    _ = unitHom f := homEquiv_pullbackUnitIso_hom f
    _ = _ := by
      apply Scheme.Modules.hom_ext
      intro U
      ext s
      let s' : Γ(𝟙_ Y.Modules, U) := s
      exact (pullbackTensorUnitObjIso_hom_app_pullbackLocalSection' f U s').symm.trans
        (Scheme.Modules.app_pullbackLocalSection f
          (Scheme.Modules.pullbackTensorUnitObjIso f).hom s')

/-- The monoidal unit comparisons obey the canonical pullback composition constraint. -/
theorem pullbackTensorUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (𝟙_ Z.Modules) ≫
      (Scheme.Modules.pullbackTensorUnitObjIso (f ≫ g)).hom =
    (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackTensorUnitObjIso g).hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso f).hom := by
  have h := Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom f g
  rw [pullbackUnitComparison, pullbackUnitComparison, pullbackUnitComparison] at h
  exact h

variable {X₀ X₁ X₂ D₀ D₁ D₂ : Scheme.{u}}
  {i₀ : D₀ ⟶ X₀} {i₁ : D₁ ⟶ X₁} {i₂ : D₂ ⟶ X₂}

/-- Commutativity of the square obtained by composing two squares. -/
theorem square_comp (f : X₁ ⟶ X₂) (g : D₁ ⟶ D₂) (w : i₁ ≫ f = g ≫ i₂)
    (f' : X₀ ⟶ X₁) (g' : D₀ ⟶ D₁) (w' : i₀ ≫ f' = g' ≫ i₁) :
    i₀ ≫ (f' ≫ f) = (g' ≫ g) ≫ i₂ := by
  rw [← Category.assoc, w', Category.assoc, w, ← Category.assoc]

/-- Pullback along consecutive commuting squares is compatibly isomorphic to pullback
along their composite square. -/
def pullbackCompIso (M : RigidifiedLineBundle i₂)
    (f : X₁ ⟶ X₂) (g : D₁ ⟶ D₂) (w : i₁ ≫ f = g ≫ i₂)
    (f' : X₀ ⟶ X₁) (g' : D₀ ⟶ D₁) (w' : i₀ ≫ f' = g' ≫ i₁) :
    Iso ((M.pullback f g w).pullback f' g' w')
      (M.pullback (f' ≫ f) (g' ≫ g) (square_comp f g w f' g' w')) where
  toIso := (Scheme.Modules.pullbackComp f' f).app M.L
  compatible := by
    have hp := Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
      f' f (f' ≫ f) rfl i₀ i₁ i₂ g' g (g' ≫ g) rfl w' w
      (square_comp f g w f' g' w') M.L
    have hn := (Scheme.Modules.pullbackComp g' g).hom.naturality M.trivialization.hom
    change (Scheme.Modules.pullback i₀).map ((Scheme.Modules.pullbackComp f' f).hom.app M.L) ≫
      (restrictionComparison (f' ≫ f) (g' ≫ g) (square_comp f g w f' g' w')).hom.app M.L ≫
      (Scheme.Modules.pullback (g' ≫ g)).map M.trivialization.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso (g' ≫ g)).hom =
      (restrictionComparison f' g' w').hom.app ((Scheme.Modules.pullback f).obj M.L) ≫
      (Scheme.Modules.pullback g').map
        ((restrictionComparison f g w).hom.app M.L ≫
          (Scheme.Modules.pullback g).map M.trivialization.hom ≫
          (Scheme.Modules.pullbackTensorUnitObjIso g).hom) ≫
      (Scheme.Modules.pullbackTensorUnitObjIso g').hom
    have hcomp :
        (restrictionComparison f' g' w').hom.app ((Scheme.Modules.pullback f).obj M.L) ≫
          (Scheme.Modules.pullback g').map ((restrictionComparison f g w).hom.app M.L) ≫
          (Scheme.Modules.pullbackComp g' g).hom.app ((Scheme.Modules.pullback i₂).obj M.L) =
        (Scheme.Modules.pullback i₀).map ((Scheme.Modules.pullbackComp f' f).hom.app M.L) ≫
          (restrictionComparison (f' ≫ f) (g' ≫ g)
            (square_comp f g w f' g' w')).hom.app M.L := by
      have hg : Scheme.Modules.pullbackCongr (rfl : g' ≫ g = g' ≫ g) =
          CategoryTheory.Iso.refl (Scheme.Modules.pullback (g' ≫ g)) := rfl
      have hf : Scheme.Modules.pullbackCongr (rfl : f' ≫ f = f' ≫ f) =
          CategoryTheory.Iso.refl (Scheme.Modules.pullback (f' ≫ f)) := rfl
      simpa only [restrictionComparison, hg, hf, CategoryTheory.Iso.trans_refl] using hp
    rw [← Category.assoc, ← hcomp]
    simp only [Category.assoc, Functor.map_comp]
    rw [← reassoc_of% hn, pullbackTensorUnit_comp]

/-- The maps on naive classes satisfy the actual pullback composition law. -/
theorem classesPullback_comp
    (f : X₁ ⟶ X₂) (g : D₁ ⟶ D₂) (w : i₁ ≫ f = g ≫ i₂)
    (f' : X₀ ⟶ X₁) (g' : D₀ ⟶ D₁) (w' : i₀ ≫ f' = g' ≫ i₁) (x : Classes i₂) :
    classesPullback f' g' w' (classesPullback f g w x) =
      classesPullback (f' ≫ f) (g' ≫ g) (square_comp f g w f' g' w') x := by
  induction x using Quotient.ind with
  | _ M => exact Quotient.sound ⟨pullbackCompIso M f g w f' g' w'⟩

/-- Pullback by the identity has the expected unit component, including its chosen comparison. -/
theorem pullbackId_unit (X : Scheme.{u}) :
    (Scheme.Modules.pullbackId X).hom.app (𝟙_ X.Modules) =
      (Scheme.Modules.pullbackTensorUnitObjIso (𝟙 X)).hom := by
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom (𝟙_ X.Modules)
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  change 𝟙 (𝟙_ X.Modules) ≫ (Scheme.Modules.pushforwardId X).inv.app (𝟙_ X.Modules) =
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app (𝟙_ X.Modules) ≫
      (Scheme.Modules.pushforward (𝟙 X)).map
        ((Scheme.Modules.pullbackId X).hom.app (𝟙_ X.Modules)) at h
  rw [Category.id_comp] at h
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  have hid :
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
        ((Scheme.Modules.pullbackId X).hom.app (𝟙_ X.Modules)) =
      (Scheme.Modules.pushforwardId X).inv.app (𝟙_ X.Modules) := by
    rw [Adjunction.homEquiv_unit]
    exact h.symm
  have heps :
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
        (Scheme.Modules.pullbackTensorUnitObjIso (𝟙 X)).hom =
      (Scheme.Modules.pushforwardId X).inv.app (𝟙_ X.Modules) := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    exact (Scheme.Modules.app_pullbackLocalSection (𝟙 X)
      (Scheme.Modules.pullbackTensorUnitObjIso (𝟙 X)).hom s).symm.trans
      (pullbackTensorUnitObjIso_hom_app_pullbackLocalSection' (𝟙 X) U s)
  exact hid.trans heps.symm

/-- The identity comparison is an isomorphism of chosen rigidifications. -/
def pullbackIdIso {X D : Scheme.{u}} {i : D ⟶ X} (M : RigidifiedLineBundle i) :
    Iso (M.pullback (𝟙 X) (𝟙 D) ((Category.comp_id i).trans (Category.id_comp i).symm)) M where
  toIso := (Scheme.Modules.pullbackId X).app M.L
  compatible := by
    have hl := NatTrans.congr_app
      (Scheme.Modules.pseudofunctor_left_unitality (f := i)) M.L
    have hr := NatTrans.congr_app
      (Scheme.Modules.pseudofunctor_right_unitality (f := i)) M.L
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hl
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hr
    change (Scheme.Modules.pullbackComp i (𝟙 X)).inv.app M.L ≫
      (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackId X).hom.app M.L) =
      (Scheme.Modules.pullbackCongr (Category.comp_id i)).hom.app M.L at hl
    change (Scheme.Modules.pullbackComp (𝟙 D) i).inv.app M.L ≫
      (Scheme.Modules.pullbackId D).hom.app ((Scheme.Modules.pullback i).obj M.L) =
      (Scheme.Modules.pullbackCongr (Category.id_comp i)).hom.app M.L at hr
    have hl' := ((Scheme.Modules.pullbackComp i (𝟙 X)).app M.L).inv_comp_eq.mp hl
    have hr' := ((Scheme.Modules.pullbackComp (𝟙 D) i).app M.L).inv_comp_eq.mp hr
    change (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackId X).hom.app M.L) =
      (Scheme.Modules.pullbackComp i (𝟙 X)).hom.app M.L ≫
      (Scheme.Modules.pullbackCongr (Category.comp_id i)).hom.app M.L at hl'
    change (Scheme.Modules.pullbackId D).hom.app ((Scheme.Modules.pullback i).obj M.L) =
      (Scheme.Modules.pullbackComp (𝟙 D) i).hom.app M.L ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp i)).hom.app M.L at hr'
    have heq :
        (Scheme.Modules.pullbackCongr
          ((Category.comp_id i).trans (Category.id_comp i).symm)).hom.app M.L ≫
          (Scheme.Modules.pullbackCongr (Category.id_comp i)).hom.app M.L =
        (Scheme.Modules.pullbackCongr (Category.comp_id i)).hom.app M.L := by
      simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans]
    change (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackId X).hom.app M.L) ≫
      M.trivialization.hom =
      (restrictionComparison (𝟙 X) (𝟙 D)
        ((Category.comp_id i).trans (Category.id_comp i).symm)).hom.app M.L ≫
      (Scheme.Modules.pullback (𝟙 D)).map M.trivialization.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso (𝟙 D)).hom
    rw [← pullbackId_unit, (Scheme.Modules.pullbackId D).hom.naturality]
    change (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackId X).hom.app M.L) ≫
      M.trivialization.hom =
      (Scheme.Modules.pullbackComp i (𝟙 X)).hom.app M.L ≫
      (Scheme.Modules.pullbackCongr
        ((Category.comp_id i).trans (Category.id_comp i).symm)).hom.app M.L ≫
      (Scheme.Modules.pullbackComp (𝟙 D) i).inv.app M.L ≫
      (Scheme.Modules.pullbackId D).hom.app ((Scheme.Modules.pullback i).obj M.L) ≫
      M.trivialization.hom
    rw [hr', Category.assoc,
      reassoc_of% (Scheme.Modules.pullbackComp (𝟙 D) i).inv_hom_id_app M.L,
      reassoc_of% heq, ← reassoc_of% hl']

theorem classesPullback_id {X D : Scheme.{u}} {i : D ⟶ X} (x : Classes i) :
    classesPullback (𝟙 X) (𝟙 D)
      ((Category.comp_id i).trans (Category.id_comp i).symm) x = x := by
  induction x using Quotient.ind with
  | _ M => exact Quotient.sound ⟨pullbackIdIso M⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
