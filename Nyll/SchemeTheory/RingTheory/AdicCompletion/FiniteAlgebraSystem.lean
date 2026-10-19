/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Effectivity of finite adic algebra systems

The algebra is the actual subalgebra of compatible sequences. Its underlying
module is identified with the compatible-sequence module, so completeness and
the transition kernels prove that it is finite. The projection kernels are
then computed as extended ideal powers. In particular, the resulting algebra
recovers every supplied algebra, including multiplication and the original
transition maps, by reduction.

This is an affine effectivity result over a complete Noetherian ring. It does
not assume an algebraization or assert algebraization on a proper scheme.
-/

noncomputable section

namespace AdicAlgebraSystem

universe u v

variable {R : Type u} [CommRing R]
  (A : ℕ → Type v) [∀ n : ℕ, CommRing (A n)] [∀ n : ℕ, Algebra R (A n)]
  (t : (n : ℕ) → A (n + 1) →ₐ[R] A n)

/-- The algebra of actual compatible sequences. -/
def sections : Subalgebra R ((n : ℕ) → A n) :=
  (AdicModuleSystem.sections A (fun n => (t n).toLinearMap)).toSubalgebra
    (fun n => (t n).map_one)
    (by
      intro x y hx hy n
      have hx' : t n (x (n + 1)) = x n := hx n
      have hy' : t n (y (n + 1)) = y n := hy n
      change t n (x (n + 1) * y (n + 1)) = x n * y n
      rw [map_mul, hx', hy'])

/-- The module comparison preserves the compatible sequence itself. -/
def sectionsLinearEquiv :
    AdicModuleSystem.sections A (fun n => (t n).toLinearMap) ≃ₗ[R] sections A t :=
  (sections A t).toSubmoduleEquiv

/-- Evaluation at a stage, as an algebra homomorphism. -/
def eval (n : ℕ) : sections A t →ₐ[R] A n :=
  (Pi.evalAlgHom R A n).comp (sections A t).val

theorem eval_apply (n : ℕ) (x : sections A t) : eval A t n x = x.val n := rfl

/-- The projections retain the given transition maps. -/
theorem transition_eval (n : ℕ) (x : sections A t) :
    t n (eval A t (n + 1) x) = eval A t n x :=
  x.property n

variable (I : Ideal R)

private theorem transition_linear_ker
    (hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (I ^ (n + 1)).map (algebraMap R (A (n + 1))))
    (n : ℕ) :
    (t n).toLinearMap.ker = I ^ (n + 1) • (⊤ : Submodule R (A (n + 1))) := by
  rw [Ideal.smul_top_eq_map]
  exact congrArg (Submodule.restrictScalars R) (hker n)

private theorem power_smul_eq_bot
    (hpow : ∀ n : ℕ, (I ^ (n + 1)).map (algebraMap R (A n)) = ⊥)
    (n : ℕ) : I ^ (n + 1) • (⊤ : Submodule R (A n)) = ⊥ := by
  rw [Ideal.smul_top_eq_map, hpow n]
  rfl

section Finite

variable [∀ n : ℕ, Module.Finite R (A n)] [IsAdicComplete I R]

/-- Each projection of the constructed algebra is surjective. -/
theorem eval_surjective
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (I ^ (n + 1)).map (algebraMap R (A (n + 1))))
    (n : ℕ) : Function.Surjective (eval A t n) := by
  intro a
  obtain ⟨x, hx⟩ := AdicModuleSystem.eval_surjective A
    (fun k => (t k).toLinearMap) I ht (transition_linear_ker A t I hker) n a
  exact ⟨sectionsLinearEquiv A t x, hx⟩

/-- The compatible-sequence algebra is finite over the complete Noetherian base. -/
theorem finite [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (I ^ (n + 1)).map (algebraMap R (A (n + 1))))
    (hpow : ∀ n : ℕ, (I ^ (n + 1)).map (algebraMap R (A n)) = ⊥) :
    Module.Finite R (sections A t) := by
  have hfinite : Module.Finite R
      (AdicModuleSystem.sections A (fun n => (t n).toLinearMap)) :=
    AdicModuleSystem.finite A (fun n => (t n).toLinearMap) I ht
      (transition_linear_ker A t I hker) (power_smul_eq_bot A I hpow)
  exact Module.Finite.of_surjective (sectionsLinearEquiv A t).toLinearMap
    (sectionsLinearEquiv A t).surjective

/-- The kernel is the extended ideal power in the constructed algebra. -/
theorem ker_eval [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (I ^ (n + 1)).map (algebraMap R (A (n + 1))))
    (hpow : ∀ n : ℕ, (I ^ (n + 1)).map (algebraMap R (A n)) = ⊥)
    (n : ℕ) : RingHom.ker (eval A t n) =
      (I ^ (n + 1)).map (algebraMap R (sections A t)) := by
  let e := sectionsLinearEquiv A t
  ext x
  change eval A t n x = 0 ↔
    x ∈ ((I ^ (n + 1)).map (algebraMap R (sections A t))).restrictScalars R
  rw [← Ideal.smul_top_eq_map]
  constructor
  · intro hx
    have hx' : e.symm x ∈
        (AdicModuleSystem.eval A (fun k => (t k).toLinearMap) n).ker := hx
    rw [AdicModuleSystem.ker_eval A (fun k => (t k).toLinearMap) I ht
      (transition_linear_ker A t I hker) (power_smul_eq_bot A I hpow) n] at hx'
    have hmap : e (e.symm x) ∈
        (I ^ (n + 1) • (⊤ : Submodule R
          (AdicModuleSystem.sections A (fun k => (t k).toLinearMap)))).map
            e.toLinearMap := Submodule.mem_map_of_mem hx'
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective] at hmap
    simpa only [LinearEquiv.apply_symm_apply] using hmap
  · intro hx
    have hz : eval A t n x ∈ I ^ (n + 1) • (⊤ : Submodule R (A n)) :=
      Submodule.smul_top_le_comap_smul_top (I ^ (n + 1)) (eval A t n).toLinearMap hx
    rw [power_smul_eq_bot A I hpow n] at hz
    exact hz

/-- Reduction of the constructed algebra recovers the supplied stage as an algebra. -/
def quotientEquiv [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (I ^ (n + 1)).map (algebraMap R (A (n + 1))))
    (hpow : ∀ n : ℕ, (I ^ (n + 1)).map (algebraMap R (A n)) = ⊥)
    (n : ℕ) :
    ((sections A t) ⧸ ((I ^ (n + 1)).map (algebraMap R (sections A t)))) ≃ₐ[R] A n :=
  (Ideal.quotientEquivAlgOfEq R (ker_eval A t I ht hker hpow n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (eval_surjective A t I ht hker n))

/-- Recovery is induced by the actual projection. -/
theorem quotientEquiv_mk [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (I ^ (n + 1)).map (algebraMap R (A (n + 1))))
    (hpow : ∀ n : ℕ, (I ^ (n + 1)).map (algebraMap R (A n)) = ⊥)
    (n : ℕ) (x : sections A t) :
    quotientEquiv A t I ht hker hpow n
      (Ideal.Quotient.mk ((I ^ (n + 1)).map (algebraMap R (sections A t))) x) =
        eval A t n x := by
  rw [quotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

end Finite

end AdicAlgebraSystem
