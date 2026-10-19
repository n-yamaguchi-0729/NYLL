/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FlatAssociatedGraded
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemAssociatedGraded
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveModuleSystem
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Original kernels of a finite projective adic system

The compatible-sequence module is constructed from the original stages.
Projectivity is proved from their projectivity over the actual quotient
rings. Scalar multiplication then identifies each original last layer
with the corresponding ideal power tensored with the first original stage.

In positive degree the target is the kernel of the original transition.
The calculation on pure tensors uses the actual projections of the given
system; no independent recovery isomorphism or flatness of the limit is
an input.
-/

noncomputable section

open scoped TensorProduct

namespace AdicModuleSystem

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (t : (n : ℕ) → M (n + 1) →ₗ[R] M n) (I : Ideal R) [IsAdicComplete I R]
  [∀ n : ℕ, Module.Finite R (M n)]
  (ht : ∀ n : ℕ, Function.Surjective (t n))
  (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
  (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)

private def firstReductionEquiv :
    ((sections M t) ⧸ (I • (⊤ : Submodule R (sections M t)))) ≃ₗ[R] M 0 :=
  (Submodule.quotEquivOfEq (I • (⊤ : Submodule R (sections M t)))
    (I ^ (0 + 1) • (⊤ : Submodule R (sections M t))) (by rw [pow_one])).trans
      (quotientEquiv M t I ht hker hpow 0)

private theorem firstReductionEquiv_mk (x : sections M t) :
    firstReductionEquiv M t I ht hker hpow (Submodule.Quotient.mk x) =
      eval M t 0 x :=
  quotientEquiv_mk M t I ht hker hpow 0 x

variable [∀ n : ℕ, Module (R ⧸ I ^ (n + 1)) (M n)]
  [∀ n : ℕ, IsScalarTower R (R ⧸ I ^ (n + 1)) (M n)]
  [∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1)) (M n)]

/-- The original degree `n` layer is the `n`th ideal power tensored
with the first original stage of the finite projective system. -/
def projectiveLayerTensorEquiv (n : ℕ) :
    ↥(I ^ n) ⊗[R] M 0 ≃ₗ[R] ↥(I ^ n • (⊤ : Submodule R (M n))) := by
  have : Module.Projective R (sections M t) := projective M t I ht hker hpow
  let e₀ := firstReductionEquiv M t I ht hker hpow
  exact (TensorProduct.congr (LinearEquiv.refl R ↥(I ^ n)) e₀.symm).trans
    ((AdicFlatLayers.layerTensorEquiv (sections M t) I n).trans
      (layerEquiv M t I ht hker hpow n))

/-- The actual tensor-layer isomorphism multiplies the original stage
value of a compatible sequence by the original ideal coefficient. -/
theorem projectiveLayerTensorEquiv_tmul_eval (n : ℕ) (a : ↥(I ^ n)) (x : sections M t) :
    (projectiveLayerTensorEquiv M t I ht hker hpow n (a ⊗ₜ[R] eval M t 0 x)).val =
      a.val • eval M t n x := by
  have : Module.Projective R (sections M t) := projective M t I ht hker hpow
  have hfirst : (firstReductionEquiv M t I ht hker hpow).symm (eval M t 0 x) =
      Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).mpr (firstReductionEquiv_mk M t I ht hker hpow x).symm
  change (layerEquiv M t I ht hker hpow n
    (AdicFlatLayers.layerTensorEquiv (sections M t) I n
      ((TensorProduct.congr (LinearEquiv.refl R ↥(I ^ n))
        (firstReductionEquiv M t I ht hker hpow).symm)
          (a ⊗ₜ[R] eval M t 0 x)))).val = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hfirst,
    AdicFlatLayers.layerTensorEquiv_tmul_mk]
  exact (layerEquiv_mk M t I ht hker hpow n
    ⟨a.val • x, Submodule.smul_mem_smul a.property
      (Submodule.mem_top : x ∈ (⊤ : Submodule R (sections M t)))⟩).trans
        ((eval M t n).map_smul a.val x)

/-- Every original transition kernel is computed from the original
first stage and the corresponding ideal power. -/
def projectiveTransitionKernelEquiv (n : ℕ) :
    ↥(I ^ (n + 1)) ⊗[R] M 0 ≃ₗ[R] (t n).ker :=
  (projectiveLayerTensorEquiv M t I ht hker hpow (n + 1)).trans
    (LinearEquiv.ofEq (I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
      (t n).ker (hker n).symm)

/-- The kernel comparison retains the original coefficient and the
actual next-stage value of the compatible sequence. -/
theorem projectiveTransitionKernelEquiv_tmul_eval
    (n : ℕ) (a : ↥(I ^ (n + 1))) (x : sections M t) :
    (projectiveTransitionKernelEquiv M t I ht hker hpow n
      (a ⊗ₜ[R] eval M t 0 x)).val = a.val • eval M t (n + 1) x :=
  projectiveLayerTensorEquiv_tmul_eval M t I ht hker hpow (n + 1) a x

end AdicModuleSystem
