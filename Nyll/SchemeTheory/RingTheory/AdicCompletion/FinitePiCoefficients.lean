/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Finite coefficient vectors in completed free modules

An infinite direct sum commutes with a finite product before completion,
and completion commutes with the finite product. The resulting concrete
equivalence identifies a matrix acting on completed free modules with
the same finite matrix acting on their coordinates.

These computation rules keep the coefficients of a finite relation
unchanged when its direct sum is completed.
-/

noncomputable section

universe u a b c

namespace AdicCompletion

variable (R : Type u) [CommRing R] (α : Type a) (ι : Type b) [Fintype ι]

/-- Transposition of a finite coefficient vector and a finitely
supported index. -/
def finsuppPiCoefficients : (α →₀ (ι → R)) ≃ₗ[R] (ι → α →₀ R) :=
  (Finsupp.mapRange.linearEquiv (Finsupp.linearEquivFunOnFinite R R ι).symm).trans
    ((Finsupp.curryLinearEquiv R).symm.trans
      ((Finsupp.domLCongr (Equiv.prodComm α ι)).trans
        ((Finsupp.curryLinearEquiv R).trans
          (Finsupp.linearEquivFunOnFinite R (α →₀ R) ι))))

/-- Transposition evaluates the original coefficient function. -/
theorem finsuppPiCoefficients_apply (x : α →₀ (ι → R)) (i : ι) (a : α) :
    finsuppPiCoefficients R α ι x i a = x a i := by
  rfl

variable {R} (I : Ideal R) [DecidableEq ι]

/-- The actual finite coefficient equivalence after adic completion. -/
def finsuppPiCompletion :
    AdicCompletion I (α →₀ (ι → R)) ≃ₗ[AdicCompletion I R]
      (ι → AdicCompletion I (α →₀ R)) :=
  (congr I (finsuppPiCoefficients R α ι)).trans
    (piEquivOfFintype I (fun _ : ι => α →₀ R))

/-- Each completed coefficient is induced by the original projection. -/
theorem finsuppPiCompletion_apply (x : AdicCompletion I (α →₀ (ι → R))) (i : ι) :
    finsuppPiCompletion α ι I x i =
      map I (Finsupp.mapRange.linearMap (α := α) (LinearMap.proj i)) x := by
  rw [finsuppPiCompletion, LinearEquiv.trans_apply, piEquivOfFintype_apply,
    congr_apply]
  change map I (LinearMap.proj i)
    (map I (finsuppPiCoefficients R α ι).toLinearMap x) = _
  rw [map_comp_apply]
  have hproj : (LinearMap.proj i).comp (finsuppPiCoefficients R α ι).toLinearMap =
      Finsupp.mapRange.linearMap (α := α) (LinearMap.proj i) := by
    apply LinearMap.ext
    intro y
    apply Finsupp.ext
    intro a
    exact finsuppPiCoefficients_apply R α ι y i a
  rw [hproj]

/-- A finite linear functional acts on a completed free module using
its original coefficients. -/
theorem map_finsupp_functional (f : (ι → R) →ₗ[R] R)
    (x : AdicCompletion I (α →₀ (ι → R))) :
    map I (Finsupp.mapRange.linearMap (α := α) f) x =
      ∑ i : ι, f (fun j => if i = j then 1 else 0) •
        finsuppPiCompletion α ι I x i := by
  have hmap : Finsupp.mapRange.linearMap (α := α) f =
      ∑ i : ι, f (fun j => if i = j then 1 else 0) •
        Finsupp.mapRange.linearMap (α := α) (LinearMap.proj i) := by
    apply LinearMap.ext
    intro y
    apply Finsupp.ext
    intro a
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    change f (y a) = ∑ i : ι, f (fun j => if i = j then 1 else 0) * y a i
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hmap, _root_.map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.map_smul, LinearMap.smul_apply, finsuppPiCompletion_apply]

/-- Matrix coefficients are preserved by the finite coefficient
equivalence after completion. -/
theorem finsuppPiCompletion_map (κ : Type c) [Fintype κ] [DecidableEq κ]
    (f : (ι → R) →ₗ[R] (κ → R))
    (x : AdicCompletion I (α →₀ (ι → R))) (k : κ) :
    finsuppPiCompletion α κ I
        (map I (Finsupp.mapRange.linearMap (α := α) f) x) k =
      ∑ i : ι, f (fun j => if i = j then 1 else 0) k •
        finsuppPiCompletion α ι I x i := by
  rw [finsuppPiCompletion_apply, map_comp_apply,
    ← Finsupp.mapRange.linearMap_comp]
  exact map_finsupp_functional α ι I ((LinearMap.proj k).comp f) x

end AdicCompletion
