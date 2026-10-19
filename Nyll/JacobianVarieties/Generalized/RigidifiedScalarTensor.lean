/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedScalarBoundary
import Nyll.JacobianVarieties.Generalized.RigidifiedCommutativity

/-! # The scalar boundary preserves actual rigidified tensor products -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

private theorem tensor_unit_end_unitor {V : Type*} [Category V] [MonoidalCategory V]
    (a b : 𝟙_ V ⟶ 𝟙_ V) :
    (a ⊗ₘ b) ≫ (λ_ (𝟙_ V)).hom = (λ_ (𝟙_ V)).hom ≫ a ≫ b := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality]
  simp only [unitors_equal, rightUnitor_naturality_assoc]

variable {X D : Scheme.{u}} (i : D ⟶ X)

/-- Multiplication of chosen scalar trivializations is realized by the actual tensor unitor. -/
def unitWithTensorIso (a b : 𝟙_ D.Modules ≅ 𝟙_ D.Modules) :
    Iso ((unitWith i a).tensor (unitWith i b)) (unitWith i (a ≪≫ b)) where
  toIso := λ_ (𝟙_ X.Modules)
  compatible := by
    let : (Scheme.Modules.pullback i).Monoidal := Scheme.Modules.pullback_monoidal i
    change (Scheme.Modules.pullback i).map (λ_ (𝟙_ X.Modules)).hom ≫
      Functor.OplaxMonoidal.η (Scheme.Modules.pullback i) ≫ a.hom ≫ b.hom =
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) (𝟙_ X.Modules) (𝟙_ X.Modules) ≫
          ((Functor.OplaxMonoidal.η (Scheme.Modules.pullback i) ≫ a.hom) ⊗ₘ
            (Functor.OplaxMonoidal.η (Scheme.Modules.pullback i) ≫ b.hom)) ≫
              (λ_ (𝟙_ D.Modules)).hom
    rw [← tensorHom_comp_tensorHom_assoc, tensor_unit_end_unitor,
      Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc, leftUnitor_naturality_assoc,
      CategoryTheory.Iso.inv_hom_id_assoc]

/-- The scalar boundary is multiplicative for the given unit and tensor structures. -/
theorem scalarClass_mul (a b : Γ(D, ⊤)ˣ) :
    scalarClass i (a * b) = scalarClass i a * scalarClass i b := by
  have hab : (unitAutEquivUnits D).symm (a * b) =
      (unitAutEquivUnits D).symm a ≪≫ (unitAutEquivUnits D).symm b := by
    apply (unitAutEquivUnits D).injective
    calc
      _ = a * b := (unitAutEquivUnits D).apply_symm_apply (a * b)
      _ = unitAutEquivUnits D ((unitAutEquivUnits D).symm a) *
          unitAutEquivUnits D ((unitAutEquivUnits D).symm b) :=
        congrArg₂ (fun x y : Γ(D, ⊤)ˣ => x * y)
          ((unitAutEquivUnits D).apply_symm_apply a).symm
          ((unitAutEquivUnits D).apply_symm_apply b).symm
      _ = _ := (unitAutEquivUnits_isoTrans D _ _).symm
  change classOf (unitWith i ((unitAutEquivUnits D).symm (a * b))) =
    classOf ((unitWith i ((unitAutEquivUnits D).symm a)).tensor
      (unitWith i ((unitAutEquivUnits D).symm b)))
  rw [hab]
  exact Quotient.sound ⟨(unitWithTensorIso i _ _).symm⟩

/-- The actual scalar boundary as a homomorphism of tensor class groups. -/
def scalarClassHom : Γ(D, ⊤)ˣ →* Classes i :=
  MonoidHom.mk' (scalarClass i) (scalarClass_mul i)

/-- The proved scalar relation descends the group homomorphism through ambient units. -/
def scalarQuotientClassHom : Γ(D, ⊤)ˣ ⧸ extendingScalars i →* Classes i :=
  QuotientGroup.lift (extendingScalars i) (scalarClassHom i) (by
    rintro a ⟨b, rfl⟩
    apply MonoidHom.mem_ker.mpr
    exact ((scalarClass_eq_iff i _ 1).mpr ⟨b, mul_one _⟩).trans
      (scalarClassHom i).map_one)

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
