/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedPullback
import Nyll.JacobianVarieties.Generalized.RigidifiedTensor
import Nyll.SchemeTheory.Modules.Sections.IhomSections
import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorObjIsoHomAppPullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Tensor coherence of rigidified pullback

The pullback composition comparison preserves the actual tensor comparison: this is
proved on locally pulled-back pure tensor sections using the canonical adjunctions.
-/

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsFrameOn_pullbackLocalSection.PicTanH

/-- The canonical pullback composition is compatible with the canonical tensor
comparison, as an equality of actual sheaf morphisms. -/
@[reassoc] theorem pullbackComp_hom_tensor {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (L M : Z.Modules) :
    (pullback f).map (pullbackTensorObjIso g L M).hom ≫
        (pullbackTensorObjIso f ((pullback g).obj L) ((pullback g).obj M)).hom ≫
        ((pullbackComp f g).hom.app L ⊗ₘ (pullbackComp f g).hom.app M) =
      (pullbackComp f g).hom.app (L ⊗ M) ≫
        (pullbackTensorObjIso (f ≫ g) L M).hom := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply tensor_hom_ext
  intro U s t
  rw [← app_pullbackLocalSection g, ← app_pullbackLocalSection g,
    ← app_pullbackLocalSection f, ← app_pullbackLocalSection f]
  simp only [Hom.comp_app, CategoryTheory.comp_apply]
  rw [← pullbackLocalSection_app, pullbackTensorObjIso_hom_app_pullbackLocalSection,
    pullbackTensorObjIso_hom_app_pullbackLocalSection, tensorHom_app_tensorSections,
    pullbackComp_hom_app_app_pullbackLocalSection,
    pullbackComp_hom_app_app_pullbackLocalSection,
    pullbackComp_hom_app_app_pullbackLocalSection]
  exact (pullbackTensorObjIso_hom_app_pullbackLocalSection (f ≫ g) s t).symm

private theorem isMonoidal_of_oplax {C C' : Type*} [Category C] [Category C']
    [MonoidalCategory C] [MonoidalCategory C']
    {F G : C ⥤ C'} [F.Monoidal] [G.Monoidal] (t : F ⟶ G)
    (hu : t.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F)
    (ht : ∀ L M : C, Functor.OplaxMonoidal.δ F L M ≫ (t.app L ⊗ₘ t.app M) =
      t.app (L ⊗ M) ≫ Functor.OplaxMonoidal.δ G L M) : t.IsMonoidal where
  unit := by
    apply (cancel_mono (Functor.OplaxMonoidal.η G)).mp
    rw [Category.assoc, hu, Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  tensor L M := by
    apply (cancel_mono (Functor.OplaxMonoidal.δ G L M)).mp
    rw [Category.assoc, ← ht, Functor.Monoidal.μ_δ_assoc, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

/-- The prescribed composition comparison is a monoidal natural transformation. -/
instance pullbackComp_hom_isMonoidal {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (pullbackComp f g).hom.IsMonoidal := by
  apply isMonoidal_of_oplax
  · change (pullbackComp f g).hom.app (𝟙_ Z.Modules) ≫
      (pullbackTensorUnitObjIso (f ≫ g)).hom =
      (pullback f).map (pullbackTensorUnitObjIso g).hom ≫
        (pullbackTensorUnitObjIso f).hom
    exact GeneralizedJacobian.RigidifiedLineBundle.pullbackTensorUnit_comp f g
  · intro L M
    change ((pullback f).map (pullbackTensorObjIso g L M).hom ≫
        (pullbackTensorObjIso f ((pullback g).obj L) ((pullback g).obj M)).hom) ≫
        ((pullbackComp f g).hom.app L ⊗ₘ (pullbackComp f g).hom.app M) =
      (pullbackComp f g).hom.app (L ⊗ M) ≫ (pullbackTensorObjIso (f ≫ g) L M).hom
    exact (Category.assoc _ _ _).trans (pullbackComp_hom_tensor f g L M)

/-- Equality transport of scheme pullbacks preserves their canonical monoidal structures. -/
instance pullbackCongr_hom_isMonoidal {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    (pullbackCongr w).hom.IsMonoidal := by
  cases w
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 (pullback f)))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X X' D D' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}

private theorem monoidal_oplax_tensor {C C' : Type*} [Category C] [Category C']
    [MonoidalCategory C] [MonoidalCategory C']
    {F G : C ⥤ C'} [F.Monoidal] [G.Monoidal] (t : F ⟶ G) [t.IsMonoidal]
    (L M : C) :
    Functor.OplaxMonoidal.δ F L M ≫ (t.app L ⊗ₘ t.app M) =
      t.app (L ⊗ M) ≫ Functor.OplaxMonoidal.δ G L M := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F L M)).mp
  rw [Functor.Monoidal.μ_δ_assoc, ← Category.assoc,
    NatTrans.IsMonoidal.tensor, Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- The square comparison preserves the canonical monoidal structures on both paths. -/
instance restrictionComparison_hom_isMonoidal
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i) :
    (restrictionComparison f g w).hom.IsMonoidal := by
  change NatTrans.IsMonoidal
    ((Scheme.Modules.pullbackComp i' f).hom ≫
      (Scheme.Modules.pullbackCongr w).hom ≫ (Scheme.Modules.pullbackComp g i).inv)
  infer_instance

/-- Pullback preserves tensor products through an isomorphism which preserves
the specified trivializations on the full modulus. -/
def pullbackTensorIso (M N : RigidifiedLineBundle i)
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i) :
    Iso ((M.tensor N).pullback f g w)
      ((M.pullback f g w).tensor (N.pullback f g w)) where
  toIso := Scheme.Modules.pullbackTensorObjIso f M.L N.L
  compatible := by
    have hk := monoidal_oplax_tensor (restrictionComparison f g w).hom M.L N.L
    change ((Scheme.Modules.pullback i').map
        (Scheme.Modules.pullbackTensorObjIso f M.L N.L).hom ≫
        (Scheme.Modules.pullbackTensorObjIso i'
          ((Scheme.Modules.pullback f).obj M.L) ((Scheme.Modules.pullback f).obj N.L)).hom) ≫
        ((restrictionComparison f g w).hom.app M.L ⊗ₘ
          (restrictionComparison f g w).hom.app N.L) =
      (restrictionComparison f g w).hom.app (M.L ⊗ N.L) ≫
        (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackTensorObjIso i M.L N.L).hom ≫
          (Scheme.Modules.pullbackTensorObjIso g
            ((Scheme.Modules.pullback i).obj M.L) ((Scheme.Modules.pullback i).obj N.L)).hom at hk
    change (Scheme.Modules.pullback i').map
        (Scheme.Modules.pullbackTensorObjIso f M.L N.L).hom ≫
        (Scheme.Modules.pullbackTensorObjIso i'
          ((Scheme.Modules.pullback f).obj M.L) ((Scheme.Modules.pullback f).obj N.L)).hom ≫
        (((restrictionComparison f g w).hom.app M.L ≫
          (Scheme.Modules.pullback g).map M.trivialization.hom ≫
          (Scheme.Modules.pullbackTensorUnitObjIso g).hom) ⊗ₘ
         ((restrictionComparison f g w).hom.app N.L ≫
          (Scheme.Modules.pullback g).map N.trivialization.hom ≫
          (Scheme.Modules.pullbackTensorUnitObjIso g).hom)) ≫ (λ_ (𝟙_ D'.Modules)).hom =
      (restrictionComparison f g w).hom.app (M.L ⊗ N.L) ≫
        (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackTensorObjIso i M.L N.L).hom ≫
            (M.trivialization.hom ⊗ₘ N.trivialization.hom) ≫ (λ_ (𝟙_ D.Modules)).hom) ≫
        (Scheme.Modules.pullbackTensorUnitObjIso g).hom
    simp only [← tensorHom_comp_tensorHom, Category.assoc, Functor.map_comp]
    rw [reassoc_of% hk]
    change (restrictionComparison f g w).hom.app (M.L ⊗ N.L) ≫
        (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackTensorObjIso i M.L N.L).hom ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g)
          ((Scheme.Modules.pullback i).obj M.L) ((Scheme.Modules.pullback i).obj N.L) ≫
        ((Scheme.Modules.pullback g).map M.trivialization.hom ⊗ₘ
          (Scheme.Modules.pullback g).map N.trivialization.hom) ≫
        (Functor.OplaxMonoidal.η (Scheme.Modules.pullback g) ⊗ₘ
          Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)) ≫ (λ_ (𝟙_ D'.Modules)).hom =
      (restrictionComparison f g w).hom.app (M.L ⊗ N.L) ≫
        (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackTensorObjIso i M.L N.L).hom ≫
        (Scheme.Modules.pullback g).map (M.trivialization.hom ⊗ₘ N.trivialization.hom) ≫
        (Scheme.Modules.pullback g).map (λ_ (𝟙_ D.Modules)).hom ≫
        Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)
    rw [Functor.OplaxMonoidal.δ_natural_assoc,
      Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc,
      leftUnitor_naturality, CategoryTheory.Iso.inv_hom_id_assoc]

/-- Maps on naive rigidified classes respect the actual tensor product. -/
theorem classesPullback_tensor (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i)
    (x y : Classes i) :
    classesPullback f g w (classesTensor x y) =
      classesTensor (classesPullback f g w x) (classesPullback f g w y) := by
  induction x using Quotient.ind with
  | _ M =>
    induction y using Quotient.ind with
    | _ N => exact Quotient.sound ⟨pullbackTensorIso M N f g w⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
