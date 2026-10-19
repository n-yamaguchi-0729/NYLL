/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedTensor
import Nyll.SchemeTheory.Modules.Sections.IhomSections
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorObjIsoHomAppPullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionBraiding
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection

/-!
# Commutativity of rigidified tensor products

The pullback tensor comparison preserves the ordinary braiding. The proof checks the
comparison on local tensor sections, using the pullback adjunction and sheafification.
Consequently the ordinary braiding preserves the chosen rigidifications, so the naive
compatible-isomorphism classes form a commutative group.
-/

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of modules preserves braiding under its canonical tensor comparison. -/
@[reassoc] theorem pullbackTensorObjIso_hom_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y) (L M : Y.Modules) :
    (pullback f).map (β_ L M).hom ≫ (pullbackTensorObjIso f M L).hom =
      (pullbackTensorObjIso f L M).hom ≫
        (β_ ((pullback f).obj L) ((pullback f).obj M)).hom := by
  apply ((pullbackPushforwardAdjunction f).homEquiv (L ⊗ M) _).injective
  apply tensor_hom_ext
  intro U s t
  rw [← app_pullbackLocalSection, ← app_pullbackLocalSection]
  simp only [Hom.comp_app, CategoryTheory.comp_apply]
  rw [← pullbackLocalSection_app, braiding_hom_app_tensorSections,
    pullbackTensorObjIso_hom_app_pullbackLocalSection,
    pullbackTensorObjIso_hom_app_pullbackLocalSection, braiding_hom_app_tensorSections]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} {i : D ⟶ X}

/-- The usual braiding respects both chosen trivializations. -/
def tensorCommIso (M N : RigidifiedLineBundle i) : Iso (M.tensor N) (N.tensor M) where
  toIso := β_ M.L N.L
  compatible := by
    change (Scheme.Modules.pullback i).map (β_ M.L N.L).hom ≫
      (Scheme.Modules.pullbackTensorObjIso i N.L M.L).hom ≫
      (N.trivialization.hom ⊗ₘ M.trivialization.hom) ≫ (λ_ (𝟙_ D.Modules)).hom =
      (Scheme.Modules.pullbackTensorObjIso i M.L N.L).hom ≫
      (M.trivialization.hom ⊗ₘ N.trivialization.hom) ≫ (λ_ (𝟙_ D.Modules)).hom
    rw [Scheme.Modules.pullbackTensorObjIso_hom_braiding_assoc,
      ← BraidedCategory.braiding_naturality_assoc, braiding_leftUnitor,
      unitors_equal]

theorem classesTensor_comm (x y : Classes i) : classesTensor x y = classesTensor y x := by
  induction x using Quotient.ind with
  | _ M =>
    induction y using Quotient.ind with
    | _ N => exact Quotient.sound ⟨tensorCommIso M N⟩

/-- Tensor product makes compatible-isomorphism classes a commutative group. -/
instance classesCommGroup : CommGroup (Classes i) where
  mul_comm := classesTensor_comm

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
