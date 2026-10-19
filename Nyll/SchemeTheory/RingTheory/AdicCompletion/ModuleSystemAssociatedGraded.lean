/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AssociatedGradedModule
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Operations

/-!
# The associated graded module of an actual adic system

The Rees quotient of the constructed compatible-sequence module is finite
and identifies with the direct sum of the last ideal-power layers of the
original finite stages. In positive degree these layers are exactly the
original transition kernels. Both the comparisons and their coefficient
formulas are derived from the original projections of the system.
-/

noncomputable section

open scoped DirectSum

namespace AdicModuleSystem

universe u v

variable {R : Type u} [CommRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n) (I : Ideal R)

/-- The actual adic filtration of the compatible-sequence module. -/
abbrev sectionsFiltration : I.Filtration (sections M t) :=
  I.stableFiltration (⊤ : Submodule R (sections M t))

/-- Projection of the current ideal power to the current original stage. -/
def layerEval (n : ℕ) :
    (sectionsFiltration M t I).N n →ₗ[R] ↥(I ^ n • (⊤ : Submodule R (M n))) :=
  LinearMap.codRestrict (I ^ n • (⊤ : Submodule R (M n)))
    ((eval M t n).domRestrict ((sectionsFiltration M t I).N n))
      (fun x => Submodule.smul_top_le_comap_smul_top (I ^ n) (eval M t n) x.property)

theorem layerEval_apply (n : ℕ) (x : (sectionsFiltration M t I).N n) :
    (layerEval M t I n x).val = eval M t n x.val := rfl

variable [∀ n : ℕ, Module.Finite R (M n)] [IsAdicComplete I R]
  (ht : ∀ n : ℕ, Function.Surjective (t n))
  (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))

include ht hker in
/-- The original stage projection reaches the entire last ideal-power layer. -/
theorem layerEval_surjective (n : ℕ) : Function.Surjective (layerEval M t I n) := by
  have hmap :
      (I ^ n • (⊤ : Submodule R (sections M t))).map (eval M t n) =
        I ^ n • (⊤ : Submodule R (M n)) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (eval_surjective M t I ht hker n)]
  intro y
  let z : M n := y.val
  have hy : z ∈ (I ^ n • (⊤ : Submodule R (sections M t))).map (eval M t n) := by
    rw [hmap]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

variable [IsNoetherianRing R]
  (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)

include ht hker hpow in
/-- The kernel of the restricted projection is precisely the next ideal power. -/
theorem ker_layerEval (n : ℕ) :
    (layerEval M t I n).ker = (sectionsFiltration M t I).gradeSubmodule n := by
  ext x
  change layerEval M t I n x = 0 ↔
    x.val ∈ I ^ (n + 1) • (⊤ : Submodule R (sections M t))
  have hiff : eval M t n x.val = 0 ↔
      x.val ∈ I ^ (n + 1) • (⊤ : Submodule R (sections M t)) := by
    rw [← LinearMap.mem_ker, ker_eval M t I ht hker hpow n]
  exact ⟨fun hx => hiff.mp (congrArg Subtype.val hx), fun hx => Subtype.ext (hiff.mpr hx)⟩

/-- Each successive quotient of the effective module is the actual last
ideal-power layer of the corresponding original stage. -/
def layerEquiv (n : ℕ) :
    (sectionsFiltration M t I).gradeModule n ≃ₗ[R]
        ↥(I ^ n • (⊤ : Submodule R (M n))) := by
  let e₁ := Submodule.quotEquivOfEq (R := R) (M := (sectionsFiltration M t I).N n)
    ((sectionsFiltration M t I).gradeSubmodule n) (layerEval M t I n).ker
    (ker_layerEval M t I ht hker hpow n).symm
  let e₂ := LinearMap.quotKerEquivOfSurjective (R := R)
    (M := (sectionsFiltration M t I).N n) (M₂ := ↥(I ^ n • (⊤ : Submodule R (M n))))
    (layerEval M t I n) (layerEval_surjective M t I ht hker n)
  exact e₁.trans e₂

/-- The layer isomorphism uses the original stage value of the representative. -/
theorem layerEquiv_mk (n : ℕ) (x : (sectionsFiltration M t I).N n) :
    (layerEquiv M t I ht hker hpow n (Submodule.Quotient.mk x)).val =
      eval M t n x.val := by
  have h := LinearMap.quotKerEquivOfSurjective_apply_mk (R := R)
    (M := (sectionsFiltration M t I).N n) (M₂ := ↥(I ^ n • (⊤ : Submodule R (M n))))
    (f := layerEval M t I n) (layerEval_surjective M t I ht hker n) x
  exact (congrArg Subtype.val h).trans (layerEval_apply M t I n x)

/-- The whole associated graded module identifies with the direct sum of
the original stage layers. -/
def associatedGradedStageEquiv :
    (sectionsFiltration M t I).associatedGraded ≃ₗ[R]
      ⨁ n : ℕ, ↥(I ^ n • (⊤ : Submodule R (M n))) :=
  (Ideal.Filtration.associatedGradedEquiv (sectionsFiltration M t I)).trans
    (DirectSum.congrLinearEquiv (fun n => layerEquiv M t I ht hker hpow n))

/-- The graded comparison preserves every original polynomial coefficient
and evaluates it using the original transition system. -/
theorem associatedGradedStageEquiv_mk
    (p : (sectionsFiltration M t I).submodule) (n : ℕ) :
    (associatedGradedStageEquiv M t I ht hker hpow (Submodule.Quotient.mk p) n).val =
      eval M t n (p.val.coeff n) := by
  change (layerEquiv M t I ht hker hpow n
    (Ideal.Filtration.associatedGradedEquiv (sectionsFiltration M t I)
      (Submodule.Quotient.mk p) n)).val = _
  rw [Ideal.Filtration.associatedGradedEquiv_mk]
  exact layerEquiv_mk M t I ht hker hpow n ⟨p.val.coeff n, p.property n⟩

include ht hker hpow in
/-- Finiteness of the concrete graded module follows from the actual
effectivity of the original adic system. -/
theorem associatedGraded_finite :
    Module.Finite (reesAlgebra I) (sectionsFiltration M t I).associatedGraded := by
  have : Module.Finite R (sections M t) := finite M t I ht hker hpow
  exact Ideal.Filtration.associatedGraded_finite (sectionsFiltration M t I)
    (I.stableFiltration_stable (⊤ : Submodule R (sections M t)))

/-- The positive-degree successive quotient of the constructed module is
the actual kernel of the corresponding original transition map. -/
def transitionKernelEquiv (n : ℕ) :
    (sectionsFiltration M t I).gradeModule (n + 1) ≃ₗ[R] (t n).ker :=
  (layerEquiv M t I ht hker hpow (n + 1)).trans
    (LinearEquiv.ofEq (I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
      (t n).ker (hker n).symm)

end AdicModuleSystem
