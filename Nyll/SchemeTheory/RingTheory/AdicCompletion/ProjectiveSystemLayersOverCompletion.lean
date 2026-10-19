/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AssociatedGradedModule
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FlatAssociatedGraded
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemOverCompletion
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveOverCompletion
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Operations

/-!
# Original transition layers without a complete coefficient ring

Complete the actual finite stages of a projective adic system. Their
compatible sequences are projective over the completed coefficient ring,
and flatness of the Noetherian completion makes this same module flat over
the original ring. Its original ideal-power quotients are the original
stages, by the proved completion comparison.

The actual layer projection then identifies each transition kernel with
the corresponding original ideal power tensored with the first stage.
The pure-tensor formula uses the original compatible sequence and its
original projections. Completeness of an affine coordinate ring is not
assumed.
-/

noncomputable section

open scoped TensorProduct

namespace AdicModuleSystem

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n) (I : Ideal R)
  [∀ n : ℕ, Module.Finite R (M n)]
  (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
  (ht : ∀ n : ℕ, Function.Surjective (t n))
  (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))

local notation "C" => sections (fun n => AdicCompletion I (M n))
  (fun n => AdicCompletion.map I (t n))

/-- Evaluate the actual completed compatible sequence in its original,
uncompleted stage, using the proved completion comparison. -/
def completedSectionsOriginalEval (n : ℕ) : C →ₗ[R] M n :=
  (eval M t n).comp (completedSectionsEquiv M t I hpow).symm.toLinearMap

omit [IsNoetherianRing R] [∀ n : ℕ, Module.Finite R (M n)] in
private theorem completedPower_restrictScalars (n : ℕ) :
    (((I.map (algebraMap R (AdicCompletion I R))) ^ (n + 1) •
      (⊤ : Submodule (AdicCompletion I R) C)).restrictScalars R) =
        I ^ (n + 1) • (⊤ : Submodule R C) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
    Submodule.restrictScalars_top]

/-- Quotienting the completed compatible-sequence module by the original
ideal power recovers the original finite stage. -/
def completedOriginalReductionEquiv (n : ℕ) :
    (C ⧸ (I ^ (n + 1) • (⊤ : Submodule R C))) ≃ₗ[R] M n :=
  let J : Submodule (AdicCompletion I R) C :=
    (I.map (algebraMap R (AdicCompletion I R))) ^ (n + 1) • ⊤
  (Submodule.quotEquivOfEq _ (J.restrictScalars R)
    (completedPower_restrictScalars M t I n).symm).trans
      ((Submodule.Quotient.restrictScalarsEquiv R J).trans
        (completedQuotientEquiv M t I hpow ht hker n))

/-- The quotient comparison retains the literal original evaluation. -/
theorem completedOriginalReductionEquiv_mk (n : ℕ) (x : C) :
    completedOriginalReductionEquiv M t I hpow ht hker n (Submodule.Quotient.mk x) =
      completedSectionsOriginalEval M t I hpow n x := by
  change completedQuotientEquiv M t I hpow ht hker n (Submodule.Quotient.mk x) = _
  exact completedQuotientEquiv_mk M t I hpow ht hker n x

include ht hker in
/-- Every original stage value is realized by a completed compatible sequence. -/
theorem completedSectionsOriginalEval_surjective (n : ℕ) :
    Function.Surjective (completedSectionsOriginalEval M t I hpow n) := by
  intro x
  obtain ⟨y, hy⟩ := (completedOriginalReductionEquiv M t I hpow ht hker n).surjective x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (I ^ (n + 1) • (⊤ : Submodule R C)) y
  exact ⟨z, (completedOriginalReductionEquiv_mk M t I hpow ht hker n z).symm.trans hy⟩

include ht hker in
/-- The original-ring kernel is the original ideal power, without a
completeness assumption on that ring. -/
theorem completedSectionsOriginalEval_ker (n : ℕ) :
    (completedSectionsOriginalEval M t I hpow n).ker =
      I ^ (n + 1) • (⊤ : Submodule R C) := by
  apply Submodule.ext
  intro x
  change completedSectionsOriginalEval M t I hpow n x = 0 ↔
    x ∈ I ^ (n + 1) • (⊤ : Submodule R C)
  rw [← completedOriginalReductionEquiv_mk M t I hpow ht hker n x,
    (completedOriginalReductionEquiv M t I hpow ht hker n).map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero]

private def completedOriginalLayerEval (n : ℕ) :
    (I.stableFiltration (⊤ : Submodule R C)).N n →ₗ[R]
      ↥(I ^ n • (⊤ : Submodule R (M n))) :=
  LinearMap.codRestrict (I ^ n • (⊤ : Submodule R (M n)))
    ((completedSectionsOriginalEval M t I hpow n).domRestrict
      ((I.stableFiltration (⊤ : Submodule R C)).N n))
    (fun x => Submodule.smul_top_le_comap_smul_top (I ^ n)
      (completedSectionsOriginalEval M t I hpow n) x.property)

include ht hker in
private theorem completedOriginalLayerEval_surjective (n : ℕ) :
    Function.Surjective (completedOriginalLayerEval M t I hpow n) := by
  have hmap : (I ^ n • (⊤ : Submodule R C)).map
      (completedSectionsOriginalEval M t I hpow n) =
        I ^ n • (⊤ : Submodule R (M n)) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr
        (completedSectionsOriginalEval_surjective M t I hpow ht hker n)]
  intro y
  have hy : y.val ∈ (I ^ n • (⊤ : Submodule R C)).map
      (completedSectionsOriginalEval M t I hpow n) := by
    rw [hmap]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

include ht hker in
private theorem completedOriginalLayerEval_ker (n : ℕ) :
    (completedOriginalLayerEval M t I hpow n).ker =
      (I.stableFiltration (⊤ : Submodule R C)).gradeSubmodule n := by
  apply Submodule.ext
  intro x
  change completedOriginalLayerEval M t I hpow n x = 0 ↔
    x.val ∈ I ^ (n + 1) • (⊤ : Submodule R C)
  have hiff : completedSectionsOriginalEval M t I hpow n x.val = 0 ↔
      x.val ∈ I ^ (n + 1) • (⊤ : Submodule R C) := by
    rw [← LinearMap.mem_ker, completedSectionsOriginalEval_ker M t I hpow ht hker n]
  exact ⟨fun hx => hiff.mp (congrArg Subtype.val hx),
    fun hx => Subtype.ext (hiff.mpr hx)⟩

private def completedOriginalLayerEquiv (n : ℕ) :
    (I.stableFiltration (⊤ : Submodule R C)).gradeModule n ≃ₗ[R]
      ↥(I ^ n • (⊤ : Submodule R (M n))) :=
  (Submodule.quotEquivOfEq _ _
    (completedOriginalLayerEval_ker M t I hpow ht hker n).symm).trans
      (LinearMap.quotKerEquivOfSurjective (completedOriginalLayerEval M t I hpow n)
        (completedOriginalLayerEval_surjective M t I hpow ht hker n))

private theorem completedOriginalLayerEquiv_mk (n : ℕ)
    (x : (I.stableFiltration (⊤ : Submodule R C)).N n) :
    (completedOriginalLayerEquiv M t I hpow ht hker n (Submodule.Quotient.mk x)).val =
      completedSectionsOriginalEval M t I hpow n x.val := by
  change (LinearMap.quotKerEquivOfSurjective (completedOriginalLayerEval M t I hpow n)
    (completedOriginalLayerEval_surjective M t I hpow ht hker n)
      (Submodule.Quotient.mk x)).val = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

private def completedOriginalFirstReductionEquiv :
    (C ⧸ (I • (⊤ : Submodule R C))) ≃ₗ[R] M 0 :=
  (Submodule.quotEquivOfEq _ (I ^ (0 + 1) • (⊤ : Submodule R C))
    (by rw [pow_one])).trans (completedOriginalReductionEquiv M t I hpow ht hker 0)

private theorem completedOriginalFirstReductionEquiv_mk (x : C) :
    completedOriginalFirstReductionEquiv M t I hpow ht hker (Submodule.Quotient.mk x) =
      completedSectionsOriginalEval M t I hpow 0 x :=
  completedOriginalReductionEquiv_mk M t I hpow ht hker 0 x

variable [∀ n : ℕ, Module (R ⧸ I ^ (n + 1)) (M n)]
  [∀ n : ℕ, IsScalarTower R (R ⧸ I ^ (n + 1)) (M n)]
  [∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1)) (M n)]

include hpow ht hker in
/-- Projectivity over the actual coefficient completion and flatness of
the Noetherian completion imply flatness over the original ring. -/
theorem completed_sections_flat_original : Module.Flat R C := by
  have : Module.Flat (AdicCompletion I R) C :=
    completed_sections_flat M t I hpow ht hker
  exact Module.Flat.trans R (AdicCompletion I R) C

/-- The actual last layer at each stage is computed from the original
first stage and the original ideal, even when the original ring is not complete. -/
def projectiveOriginalLayerTensorEquiv (n : ℕ) :
    ↥(I ^ n) ⊗[R] M 0 ≃ₗ[R] ↥(I ^ n • (⊤ : Submodule R (M n))) := by
  have : Module.Flat R C := completed_sections_flat_original M t I hpow ht hker
  exact (TensorProduct.congr (LinearEquiv.refl R ↥(I ^ n))
    (completedOriginalFirstReductionEquiv M t I hpow ht hker).symm).trans
      ((AdicFlatLayers.layerTensorEquiv C I n).trans
        (completedOriginalLayerEquiv M t I hpow ht hker n))

/-- A pure tensor retains the original scalar coefficient and original
stage value of the given compatible sequence. -/
theorem projectiveOriginalLayerTensorEquiv_tmul_eval (n : ℕ)
    (a : ↥(I ^ n)) (x : sections M t) :
    (projectiveOriginalLayerTensorEquiv M t I hpow ht hker n
      (a ⊗ₜ[R] eval M t 0 x)).val = a.val • eval M t n x := by
  have : Module.Flat R C := completed_sections_flat_original M t I hpow ht hker
  let z : C := completedSectionsEquiv M t I hpow x
  have heval (k : ℕ) : completedSectionsOriginalEval M t I hpow k z = eval M t k x :=
    congrArg (eval M t k) ((completedSectionsEquiv M t I hpow).symm_apply_apply x)
  have hfirst : (completedOriginalFirstReductionEquiv M t I hpow ht hker).symm
      (eval M t 0 x) = Submodule.Quotient.mk z :=
    (LinearEquiv.symm_apply_eq _).mpr
      ((completedOriginalFirstReductionEquiv_mk M t I hpow ht hker z).trans (heval 0)).symm
  change (completedOriginalLayerEquiv M t I hpow ht hker n
    (AdicFlatLayers.layerTensorEquiv C I n
      ((TensorProduct.congr (LinearEquiv.refl R ↥(I ^ n))
        (completedOriginalFirstReductionEquiv M t I hpow ht hker).symm)
          (a ⊗ₜ[R] eval M t 0 x)))).val = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hfirst,
    AdicFlatLayers.layerTensorEquiv_tmul_mk, completedOriginalLayerEquiv_mk]
  exact ((completedSectionsOriginalEval M t I hpow n).map_smul a.val z).trans
    (congrArg (fun y : M n => a.val • y) (heval n))

/-- The kernel of each original transition is the corresponding original
ideal power tensored with the original first stage. -/
def projectiveOriginalTransitionKernelEquiv (n : ℕ) :
    ↥(I ^ (n + 1)) ⊗[R] M 0 ≃ₗ[R] (t n).ker :=
  (projectiveOriginalLayerTensorEquiv M t I hpow ht hker (n + 1)).trans
    (LinearEquiv.ofEq _ _ (hker n).symm)

/-- The transition-kernel comparison retains literal original projections. -/
theorem projectiveOriginalTransitionKernelEquiv_tmul_eval (n : ℕ)
    (a : ↥(I ^ (n + 1))) (x : sections M t) :
    (projectiveOriginalTransitionKernelEquiv M t I hpow ht hker n
      (a ⊗ₜ[R] eval M t 0 x)).val = a.val • eval M t (n + 1) x :=
  projectiveOriginalLayerTensorEquiv_tmul_eval M t I hpow ht hker (n + 1) a x

end AdicModuleSystem
