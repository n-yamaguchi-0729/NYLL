/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Tensor operations on chosen rigidifications

The rigidification on a dual is constructed from evaluation and the original chosen
trivialization. Thus evaluation preserves the chosen trivializations by construction;
no arbitrary pullback comparison for duals is assumed to have this property.
-/

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} {i : D ⟶ X}

/-- Tensoring two compatible isomorphisms preserves their chosen trivializations. -/
def Iso.tensor {M M' N N' : RigidifiedLineBundle i} (e : Iso M M') (f : Iso N N') :
    Iso (M.tensor N) (M'.tensor N') where
  toIso := e.toIso ⊗ᵢ f.toIso
  compatible := by
    let : (Scheme.Modules.pullback i).Monoidal := Scheme.Modules.pullback_monoidal i
    change (Scheme.Modules.pullback i).map (e.toIso.hom ⊗ₘ f.toIso.hom) ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) M'.L N'.L ≫
      (M'.trivialization.hom ⊗ₘ N'.trivialization.hom) ≫ (λ_ (𝟙_ D.Modules)).hom =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) M.L N.L ≫
      (M.trivialization.hom ⊗ₘ N.trivialization.hom) ≫ (λ_ (𝟙_ D.Modules)).hom
    rw [← Functor.OplaxMonoidal.δ_natural_assoc,
      tensorHom_comp_tensorHom_assoc, e.compatible, f.compatible]

/-- The left unitor respects the chosen rigidifications. -/
def unitTensorIso (M : RigidifiedLineBundle i) : Iso ((unit i).tensor M) M where
  toIso := λ_ M.L
  compatible := by
    let : (Scheme.Modules.pullback i).Monoidal := Scheme.Modules.pullback_monoidal i
    change (Scheme.Modules.pullback i).map (λ_ M.L).hom ≫ M.trivialization.hom =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) (𝟙_ X.Modules) M.L ≫
      (Functor.OplaxMonoidal.η (Scheme.Modules.pullback i) ⊗ₘ M.trivialization.hom) ≫
      (λ_ (𝟙_ D.Modules)).hom
    rw [Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc,
      leftUnitor_naturality, CategoryTheory.Iso.inv_hom_id_assoc]

/-- The right unitor respects the chosen rigidifications. -/
def tensorUnitIso (M : RigidifiedLineBundle i) : Iso (M.tensor (unit i)) M where
  toIso := ρ_ M.L
  compatible := by
    let : (Scheme.Modules.pullback i).Monoidal := Scheme.Modules.pullback_monoidal i
    change (Scheme.Modules.pullback i).map (ρ_ M.L).hom ≫ M.trivialization.hom =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) M.L (𝟙_ X.Modules) ≫
      (M.trivialization.hom ⊗ₘ Functor.OplaxMonoidal.η (Scheme.Modules.pullback i)) ≫
      (λ_ (𝟙_ D.Modules)).hom
    rw [Functor.OplaxMonoidal.δ_comp_tensorHom_η_assoc, unitors_equal,
      rightUnitor_naturality, CategoryTheory.Iso.inv_hom_id_assoc]

/-- Multiplication on naive compatible-isomorphism classes. -/
def classesTensor : Classes i → Classes i → Classes i :=
  Quotient.map₂ tensor (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨e.tensor f⟩)

@[simp] theorem classesTensor_classOf (M N : RigidifiedLineBundle i) :
    classesTensor (classOf M) (classOf N) = classOf (M.tensor N) := rfl

theorem classesTensor_unit_left (x : Classes i) :
    classesTensor (classOf (unit i)) x = x := by
  induction x using Quotient.ind with
  | _ M => exact Quotient.sound ⟨unitTensorIso M⟩

theorem classesTensor_unit_right (x : Classes i) :
    classesTensor x (classOf (unit i)) = x := by
  induction x using Quotient.ind with
  | _ M => exact Quotient.sound ⟨tensorUnitIso M⟩

private theorem tensorTrivializationInverse_cancel {C : Type*} [Category C]
    [MonoidalCategory C] {A B : C} (a : A ≅ 𝟙_ C) (r : A ⊗ B ⟶ 𝟙_ C) :
    (a.hom ⊗ₘ ((λ_ B).inv ≫ (a.inv ⊗ₘ 𝟙 B) ≫ r)) ≫ (λ_ (𝟙_ C)).hom = r := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality]
  simp only [CategoryTheory.Iso.hom_inv_id_assoc,
    ← tensorHom_id, tensorHom_comp_tensorHom_assoc, a.hom_inv_id,
    id_tensorHom_id, Category.id_comp]

/-- The evaluation isomorphism supplied by invertibility of the underlying sheaf. -/
def evaluation (M : RigidifiedLineBundle i) : M.L ⊗ Scheme.Modules.dual M.L ≅ 𝟙_ X.Modules :=
  M.isInvertible.dual.2.some

/-- The dual has the unique trivialization compatible with the chosen evaluation and `M`. -/
def dual (M : RigidifiedLineBundle i) : RigidifiedLineBundle i where
  L := Scheme.Modules.dual M.L
  isInvertible := M.isInvertible.dual.1
  trivialization := (λ_ ((Scheme.Modules.pullback i).obj (Scheme.Modules.dual M.L))).symm ≪≫
    (M.trivialization.symm ⊗ᵢ CategoryTheory.Iso.refl _) ≪≫
    (Scheme.Modules.pullbackTensorObjIso i M.L (Scheme.Modules.dual M.L)).symm ≪≫
    (Scheme.Modules.pullback i).mapIso M.evaluation ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso i

/-- Evaluation is an isomorphism of rigidified line bundles, not just underlying sheaves. -/
def tensorDualIso (M : RigidifiedLineBundle i) : Iso (M.tensor M.dual) (unit i) where
  toIso := M.evaluation
  compatible := by
    change (Scheme.Modules.pullback i).map M.evaluation.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom =
      (Scheme.Modules.pullbackTensorObjIso i M.L (Scheme.Modules.dual M.L)).hom ≫
      (M.trivialization.hom ⊗ₘ
        ((λ_ ((Scheme.Modules.pullback i).obj (Scheme.Modules.dual M.L))).inv ≫
          (M.trivialization.inv ⊗ₘ 𝟙 _) ≫
          (Scheme.Modules.pullbackTensorObjIso i M.L (Scheme.Modules.dual M.L)).inv ≫
          (Scheme.Modules.pullback i).map M.evaluation.hom ≫
          (Scheme.Modules.pullbackTensorUnitObjIso i).hom)) ≫ (λ_ (𝟙_ D.Modules)).hom
    rw [tensorTrivializationInverse_cancel, CategoryTheory.Iso.hom_inv_id_assoc]

private theorem tensorTrivialization_assoc {C : Type*} [Category C] [MonoidalCategory C]
    {A B E : C} (a : A ⟶ 𝟙_ C) (b : B ⟶ 𝟙_ C) (c : E ⟶ 𝟙_ C) :
    (α_ A B E).hom ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ (λ_ (𝟙_ C)).hom)) ≫ (λ_ (𝟙_ C)).hom =
      (((a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom) ⊗ₘ c) ≫ (λ_ (𝟙_ C)).hom := by
  rw [← tensorHom_comp_whiskerLeft a (b ⊗ₘ c) (λ_ (𝟙_ C)).hom,
    ← tensorHom_comp_whiskerRight (a ⊗ₘ b) (λ_ (𝟙_ C)).hom c]
  simp only [Category.assoc]
  rw [← associator_naturality_assoc, triangle_assoc, ← unitors_equal]

private theorem mappedTensorTrivialization_assoc {C C' : Type*} [Category C] [Category C']
    [MonoidalCategory C] [MonoidalCategory C'] (F : C ⥤ C') [F.Monoidal]
    (A B E : C) (a : F.obj A ⟶ 𝟙_ C') (b : F.obj B ⟶ 𝟙_ C')
    (c : F.obj E ⟶ 𝟙_ C') :
    F.map (α_ A B E).hom ≫ Functor.OplaxMonoidal.δ F A (B ⊗ E) ≫
      (a ⊗ₘ (Functor.OplaxMonoidal.δ F B E ≫
        (b ⊗ₘ c) ≫ (λ_ (𝟙_ C')).hom)) ≫ (λ_ (𝟙_ C')).hom =
      Functor.OplaxMonoidal.δ F (A ⊗ B) E ≫
      ((Functor.OplaxMonoidal.δ F A B ≫
        (a ⊗ₘ b) ≫ (λ_ (𝟙_ C')).hom) ⊗ₘ c) ≫ (λ_ (𝟙_ C')).hom := by
  rw [← whiskerLeft_comp_tensorHom a (Functor.OplaxMonoidal.δ F B E)
      ((b ⊗ₘ c) ≫ (λ_ (𝟙_ C')).hom),
    ← whiskerRight_comp_tensorHom (Functor.OplaxMonoidal.δ F A B)
      ((a ⊗ₘ b) ≫ (λ_ (𝟙_ C')).hom) c]
  simp only [Category.assoc]
  rw [← Functor.OplaxMonoidal.associativity_assoc, tensorTrivialization_assoc]

/-- The ordinary associator respects the three chosen trivializations. -/
def tensorAssocIso (M N P : RigidifiedLineBundle i) :
    Iso ((M.tensor N).tensor P) (M.tensor (N.tensor P)) where
  toIso := α_ M.L N.L P.L
  compatible := by
    let : (Scheme.Modules.pullback i).Monoidal := Scheme.Modules.pullback_monoidal i
    exact mappedTensorTrivialization_assoc (Scheme.Modules.pullback i) M.L N.L P.L
      M.trivialization.hom N.trivialization.hom P.trivialization.hom

theorem classesTensor_assoc (x y z : Classes i) :
    classesTensor (classesTensor x y) z = classesTensor x (classesTensor y z) := by
  induction x using Quotient.ind with
  | _ M =>
    induction y using Quotient.ind with
    | _ N =>
      induction z using Quotient.ind with
      | _ P => exact Quotient.sound ⟨tensorAssocIso M N P⟩

instance classesMul : Mul (Classes i) := ⟨classesTensor⟩

instance classesOne : One (Classes i) := ⟨classOf (unit i)⟩

/-- Choose a representative only to define the inverse operation; the group axioms prove
that the resulting class is independent of that choice. -/
instance classesInv : Inv (Classes i) := ⟨fun x => classOf (dual (Quotient.out x))⟩

private theorem classes_mul_inv (x : Classes i) : x * x⁻¹ = 1 := by
  change classesTensor x (classOf (dual (Quotient.out x))) = classOf (unit i)
  have hx : classOf (Quotient.out x) = x := Quotient.out_eq x
  calc
    _ = classesTensor (classOf (Quotient.out x))
        (classOf (dual (Quotient.out x))) :=
      congrArg (fun y => classesTensor y (classOf (dual (Quotient.out x)))) hx.symm
    _ = classOf (unit i) := Quotient.sound ⟨tensorDualIso (Quotient.out x)⟩

/-- The naive classes form a group under tensor product, with the chosen dual as inverse. -/
instance classesGroup : Group (Classes i) :=
  Group.ofRightAxioms classesTensor_assoc classesTensor_unit_right classes_mul_inv

/-- Every specified line bundle represents its categorical dual as the group inverse. -/
theorem classOf_dual (M : RigidifiedLineBundle i) : classOf M.dual = (classOf M)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  exact Quotient.sound ⟨tensorDualIso M⟩

/-- Compatible isomorphisms also identify the specifically constructed duals. -/
theorem dual_congr {M N : RigidifiedLineBundle i} (e : Iso M N) :
    Nonempty (Iso M.dual N.dual) := by
  apply (classOf_eq_iff M.dual N.dual).mp
  rw [classOf_dual, classOf_dual, (classOf_eq_iff M N).mpr ⟨e⟩]

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
