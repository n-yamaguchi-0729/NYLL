/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AssociatedGradedModule
import Nyll.SchemeTheory.RingTheory.AdicCompletion.TensorIdealQuotient
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# The actual associated graded layers of a flat module

Flatness identifies the tensor product of an ideal with the module with
its actual ideal multiple. After reduction, this identifies the degree
`n` layer with `I^n` tensored with the original degree-zero reduction.
The identification and its pure-tensor formula are constructed from
multiplication and the original submodule quotients.

For a finite locally free formal module this expresses all successive
layers in terms of its first reduction and the Rees module of the base.
It is the affine tensor calculation for the uniform Serre argument.
-/

noncomputable section

open scoped TensorProduct

namespace AdicFlatLayers

universe u v

variable {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (J : Ideal R)

/-- The original scalar multiplication map on the tensor product with an ideal. -/
def idealTensorMap : J ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp (J.subtype.rTensor M)

/-- Scalar multiplication on an original pure tensor. -/
theorem idealTensorMap_tmul (a : J) (x : M) :
    idealTensorMap M J (a ⊗ₜ[R] x) = a.val • x := rfl

/-- The image consists precisely of the actual ideal multiple of the module. -/
theorem range_idealTensorMap :
    (idealTensorMap M J).range = J • (⊤ : Submodule R M) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
        exact Submodule.smul_mem_smul a.property (Submodule.mem_top : x ∈ (⊤ : Submodule R M))
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro a ha x _hx
    exact ⟨⟨a, ha⟩ ⊗ₜ[R] x, idealTensorMap_tmul M J ⟨a, ha⟩ x⟩

variable [Module.Flat R M]

/-- Flatness makes the original scalar multiplication map injective. -/
theorem idealTensorMap_injective : Function.Injective (idealTensorMap M J) :=
  (TensorProduct.lid R M).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := M) J.subtype
      (Submodule.injective_subtype J))

/-- Tensoring the original ideal gives the actual ideal multiple of the flat module. -/
def idealTensorEquiv : J ⊗[R] M ≃ₗ[R] ↥(J • (⊤ : Submodule R M)) :=
  (LinearEquiv.ofInjective (idealTensorMap M J) (idealTensorMap_injective M J)).trans
    (LinearEquiv.ofEq _ _ (range_idealTensorMap M J))

/-- The isomorphism is induced by the original scalar multiplication. -/
theorem idealTensorEquiv_tmul (a : J) (x : M) :
    (idealTensorEquiv M J (a ⊗ₜ[R] x)).val = a.val • x := rfl

variable (I : Ideal R)

omit [Module.Flat R M] in
/-- The next power inside the current power is the intrinsic ideal multiple
of the current submodule. -/
theorem gradeSubmodule_eq_smul_top (n : ℕ) :
    (I.stableFiltration (⊤ : Submodule R M)).gradeSubmodule n =
      I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))) := by
  let P : Submodule R M := I ^ n • ⊤
  have hmap : (I • (⊤ : Submodule R P)).map P.subtype =
      I ^ (n + 1) • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    change I • (I ^ n • (⊤ : Submodule R M)) = I ^ (n + 1) • ⊤
    rw [smul_smul, pow_succ']
  change (I ^ (n + 1) • (⊤ : Submodule R M)).comap P.subtype = I • ⊤
  rw [← hmap, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype P)]

/-- Every associated graded layer is the original ideal power tensored
with the original degree-zero reduction of the flat module. -/
def layerTensorEquiv (n : ℕ) :
    ↥(I ^ n) ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R]
      (I.stableFiltration (⊤ : Submodule R M)).gradeModule n := by
  let P : Submodule R M := (I.stableFiltration (⊤ : Submodule R M)).N n
  let e := idealTensorEquiv M (I ^ n)
  have hmap : (I • (⊤ : Submodule R (↥(I ^ n) ⊗[R] M))).map e.toLinearMap =
      I • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
    rfl
  let e₁ := TensorProduct.tensorIdealQuotientEquiv I ↥(I ^ n) M
  let e₂ := Submodule.Quotient.equiv
    (I • (⊤ : Submodule R (↥(I ^ n) ⊗[R] M))) (I • (⊤ : Submodule R P)) e hmap
  let e₃ := Submodule.quotEquivOfEq (R := R)
    (M := (I.stableFiltration (⊤ : Submodule R M)).N n)
    (I • (⊤ : Submodule R ((I.stableFiltration (⊤ : Submodule R M)).N n)))
    ((I.stableFiltration (⊤ : Submodule R M)).gradeSubmodule n)
    (gradeSubmodule_eq_smul_top M I n).symm
  exact e₁.trans (e₂.trans e₃)

/-- The layer comparison multiplies the original ideal element and module
representative before taking its class in the actual successive quotient. -/
theorem layerTensorEquiv_tmul_mk (n : ℕ) (a : ↥(I ^ n)) (x : M) :
    layerTensorEquiv M I n (a ⊗ₜ[R] Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨a.val • x, Submodule.smul_mem_smul a.property
          (Submodule.mem_top : x ∈ (⊤ : Submodule R M))⟩ :
            (I.stableFiltration (⊤ : Submodule R M)).N n) := by
  simp only [layerTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.tensorIdealQuotientEquiv_tmul_mk]
  rfl

end AdicFlatLayers
