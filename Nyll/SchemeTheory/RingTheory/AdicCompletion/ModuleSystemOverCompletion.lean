/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.NilpotentModule
import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Operations

/-!
# Adic module systems over an affine coefficient completion

The coefficient ring of an affine open in a proper scheme need not be
complete. Complete each actual finite stage instead: annihilation by an
ideal power makes its completion map an isomorphism, while the native
completion functor supplies the compatible action of the completed ring.

The transition maps retain their surjectivity and their actual adic kernels.
Consequently their compatible sequences form a finite module over the
completed coefficient ring. An explicit linear equivalence recovers the
original compatible sequences. No completeness of the original ring, new
scalar action on the original stages, or effective module is assumed.
-/

noncomputable section

namespace AdicModuleSystem

universe u v

variable {R : Type u} [CommRing R]
  (M : ℕ → Type v) [∀ k : ℕ, AddCommGroup (M k)] [∀ k : ℕ, Module R (M k)]
  (t : ∀ k : ℕ, M (k + 1) →ₗ[R] M k) (I : Ideal R)
  (hpow : ∀ k : ℕ, I ^ (k + 1) • (⊤ : Submodule R (M k)) = ⊥)

private def stageCompletionEquiv (k : ℕ) : M k ≃ₗ[R] AdicCompletion I (M k) := by
  have : IsAdicComplete I (M k) :=
    IsAdicComplete.of_pow_smul_top_eq_bot I (M k) (k + 1) (hpow k)
  exact AdicCompletion.ofLinearEquiv I (M k)

private theorem stageCompletionEquiv_apply (k : ℕ) (x : M k) :
    stageCompletionEquiv M I hpow k x = AdicCompletion.of I (M k) x := rfl

/-- Completing the stages preserves the original module of compatible sequences. -/
def completedSectionsEquiv :
    sections M t ≃ₗ[R]
      sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k)) where
  toFun x := ⟨fun k => stageCompletionEquiv M I hpow k (x.val k), by
    intro k
    change AdicCompletion.map I (t k) (AdicCompletion.of I (M (k + 1)) (x.val (k + 1))) =
      AdicCompletion.of I (M k) (x.val k)
    rw [AdicCompletion.map_of, x.property k]⟩
  invFun y := ⟨fun k => (stageCompletionEquiv M I hpow k).symm (y.val k), by
    intro k
    apply (stageCompletionEquiv M I hpow k).injective
    calc
      stageCompletionEquiv M I hpow k
          (t k ((stageCompletionEquiv M I hpow (k + 1)).symm (y.val (k + 1)))) =
          AdicCompletion.map I (t k)
            (stageCompletionEquiv M I hpow (k + 1)
              ((stageCompletionEquiv M I hpow (k + 1)).symm (y.val (k + 1)))) :=
        (AdicCompletion.map_of I (t k) _).symm
      _ = AdicCompletion.map I (t k) (y.val (k + 1)) := by
        rw [LinearEquiv.apply_symm_apply]
      _ = y.val k := y.property k
      _ = stageCompletionEquiv M I hpow k
          ((stageCompletionEquiv M I hpow k).symm (y.val k)) :=
        ((stageCompletionEquiv M I hpow k).apply_symm_apply (y.val k)).symm⟩
  left_inv x := by
    apply Subtype.ext
    funext k
    exact (stageCompletionEquiv M I hpow k).symm_apply_apply (x.val k)
  right_inv y := by
    apply Subtype.ext
    funext k
    exact (stageCompletionEquiv M I hpow k).apply_symm_apply (y.val k)
  map_add' x y := by
    apply Subtype.ext
    funext k
    exact (stageCompletionEquiv M I hpow k).map_add (x.val k) (y.val k)
  map_smul' r x := by
    apply Subtype.ext
    funext k
    exact (stageCompletionEquiv M I hpow k).map_smul r (x.val k)

/-- The comparison keeps the literal completion of every original stage value. -/
theorem completedSectionsEquiv_apply (x : sections M t) (k : ℕ) :
    (completedSectionsEquiv M t I hpow x).val k = AdicCompletion.of I (M k) (x.val k) :=
  stageCompletionEquiv_apply M I hpow k (x.val k)

include hpow in
private theorem pow_smul_completed_stage (k : ℕ) :
    I ^ (k + 1) • (⊤ : Submodule R (AdicCompletion I (M k))) = ⊥ := by
  have hsurj : Function.Surjective (AdicCompletion.of I (M k)) :=
    (stageCompletionEquiv M I hpow k).surjective
  have h := congrArg (Submodule.map (AdicCompletion.of I (M k))) (hpow k)
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj,
    Submodule.map_bot] at h
  exact h

include hpow in
/-- The extended ideal annihilates each completed stage to the prescribed power. -/
theorem completed_stage_annihilation (k : ℕ) :
    (I.map (algebraMap R (AdicCompletion I R))) ^ (k + 1) •
      (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I (M k))) = ⊥ := by
  apply Submodule.restrictScalars_injective R (AdicCompletion I R) (AdicCompletion I (M k))
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
    Submodule.restrictScalars_top, Submodule.restrictScalars_bot]
  exact pow_smul_completed_stage M I hpow k

include hpow in
/-- Surjectivity of the actual transition is preserved after completing its stages. -/
theorem completed_transition_surjective
    (ht : ∀ k : ℕ, Function.Surjective (t k)) (k : ℕ) :
    Function.Surjective (AdicCompletion.map I (t k)) := by
  intro y
  obtain ⟨x, rfl⟩ := (stageCompletionEquiv M I hpow k).surjective y
  obtain ⟨a, ha⟩ := ht k x
  refine ⟨stageCompletionEquiv M I hpow (k + 1) a, ?_⟩
  rw [stageCompletionEquiv_apply, AdicCompletion.map_of, ha]
  exact (stageCompletionEquiv_apply M I hpow k x).symm

include hpow in
/-- The completed transition has exactly the extended original adic kernel. -/
theorem completed_transition_kernel
    (hker : ∀ k : ℕ, (t k).ker = I ^ (k + 1) • (⊤ : Submodule R (M (k + 1))))
    (k : ℕ) :
    (AdicCompletion.map I (t k)).ker =
      (I.map (algebraMap R (AdicCompletion I R))) ^ (k + 1) •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I (M (k + 1)))) := by
  apply Submodule.restrictScalars_injective R (AdicCompletion I R)
    (AdicCompletion I (M (k + 1)))
  rw [← LinearMap.ker_restrictScalars, ← Ideal.map_pow,
    Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := (stageCompletionEquiv M I hpow (k + 1)).surjective x
    have ha : a ∈ (t k).ker := by
      apply LinearMap.mem_ker.mpr
      apply (stageCompletionEquiv M I hpow k).injective
      rw [map_zero, stageCompletionEquiv_apply]
      exact (AdicCompletion.map_of I (t k) a).symm.trans (LinearMap.mem_ker.mp hx)
    rw [hker k] at ha
    exact Submodule.smul_top_le_comap_smul_top (I ^ (k + 1))
      (AdicCompletion.of I (M (k + 1))) ha
  · intro x hx
    have h := Submodule.smul_top_le_comap_smul_top (I ^ (k + 1))
      ((AdicCompletion.map I (t k)).restrictScalars R) hx
    change AdicCompletion.map I (t k) x ∈
      I ^ (k + 1) • (⊤ : Submodule R (AdicCompletion I (M k))) at h
    rw [pow_smul_completed_stage M I hpow k] at h
    exact LinearMap.mem_ker.mpr h

include hpow in
/-- Over a Noetherian affine coefficient ring, the actual completed system
is effective as a finite module over its coefficient completion. -/
theorem completed_sections_finite [IsNoetherianRing R]
    [∀ k : ℕ, Module.Finite R (M k)]
    (ht : ∀ k : ℕ, Function.Surjective (t k))
    (hker : ∀ k : ℕ, (t k).ker = I ^ (k + 1) • (⊤ : Submodule R (M (k + 1)))) :
    Module.Finite (AdicCompletion I R)
      (sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))) := by
  have : IsNoetherianRing (AdicCompletion I R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing I
  have hcomplete : IsAdicComplete I (AdicCompletion I R) :=
    AdicCompletion.isAdicComplete (I := I) (M := R) (IsNoetherian.noetherian I)
  have : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    (IsAdicComplete.map_algebraMap_iff (I := I)
      (S := AdicCompletion I R) (M := AdicCompletion I R)).mpr hcomplete
  have : ∀ k : ℕ, Module.Finite (AdicCompletion I R) (AdicCompletion I (M k)) := by
    intro k
    exact Module.Finite.of_surjective (AdicCompletion.ofTensorProduct I (M k))
      (AdicCompletion.ofTensorProduct_surjective_of_finite I (M k))
  exact finite (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))
    (I.map (algebraMap R (AdicCompletion I R)))
    (completed_transition_surjective M t I hpow ht)
    (completed_transition_kernel M t I hpow hker)
    (completed_stage_annihilation M I hpow)

/-- Reduction of the effective module over the coefficient completion recovers
the original, uncompleted stage as an `R`-module. -/
def completedQuotientEquiv [IsNoetherianRing R]
    [∀ k : ℕ, Module.Finite R (M k)]
    (ht : ∀ k : ℕ, Function.Surjective (t k))
    (hker : ∀ k : ℕ, (t k).ker = I ^ (k + 1) • (⊤ : Submodule R (M (k + 1))))
    (n : ℕ) :
    ((sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))) ⧸
      ((I.map (algebraMap R (AdicCompletion I R))) ^ (n + 1) •
        (⊤ : Submodule (AdicCompletion I R)
          (sections (fun k => AdicCompletion I (M k))
            (fun k => AdicCompletion.map I (t k)))))) ≃ₗ[R] M n := by
  have : IsNoetherianRing (AdicCompletion I R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing I
  have hcomplete : IsAdicComplete I (AdicCompletion I R) :=
    AdicCompletion.isAdicComplete (I := I) (M := R) (IsNoetherian.noetherian I)
  have : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    (IsAdicComplete.map_algebraMap_iff (I := I)
      (S := AdicCompletion I R) (M := AdicCompletion I R)).mpr hcomplete
  have : ∀ k : ℕ, Module.Finite (AdicCompletion I R) (AdicCompletion I (M k)) := by
    intro k
    exact Module.Finite.of_surjective (AdicCompletion.ofTensorProduct I (M k))
      (AdicCompletion.ofTensorProduct_surjective_of_finite I (M k))
  exact ((quotientEquiv (fun k => AdicCompletion I (M k))
    (fun k => AdicCompletion.map I (t k)) (I.map (algebraMap R (AdicCompletion I R)))
    (completed_transition_surjective M t I hpow ht)
    (completed_transition_kernel M t I hpow hker)
    (completed_stage_annihilation M I hpow) n).restrictScalars R).trans
      (stageCompletionEquiv M I hpow n).symm

/-- The reduction comparison is induced by the literal original stage value
of the corresponding compatible sequence. -/
theorem completedQuotientEquiv_mk [IsNoetherianRing R]
    [∀ k : ℕ, Module.Finite R (M k)]
    (ht : ∀ k : ℕ, Function.Surjective (t k))
    (hker : ∀ k : ℕ, (t k).ker = I ^ (k + 1) • (⊤ : Submodule R (M (k + 1))))
    (n : ℕ)
    (x : sections (fun k => AdicCompletion I (M k))
      (fun k => AdicCompletion.map I (t k))) :
    completedQuotientEquiv M t I hpow ht hker n (Submodule.Quotient.mk x) =
      ((completedSectionsEquiv M t I hpow).symm x).val n := by
  simp only [completedQuotientEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientEquiv_mk]
  rfl

end AdicModuleSystem
