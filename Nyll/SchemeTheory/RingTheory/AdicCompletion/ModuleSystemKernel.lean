/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.KernelStabilization
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemHom
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Kernels of actual effective adic module systems

A compatible family of maps acts on the constructed modules of compatible
sequences. Its kernel is finite. Artin--Rees identifies its image in each
original stage with the image of every sufficiently late stage kernel,
using the actual composites of the supplied transitions.

A second bound recovers the intrinsic adic quotients of this kernel from
those stable images. The recovery maps retain the original element and
the original evaluation in the given system. The effective modules,
stable images, and quotient comparisons are all constructed.

These are the affine kernel stabilization statements used in
https://stacks.math.columbia.edu/tag/087X.
-/

noncomputable section

open CategoryTheory Opposite

namespace AdicModuleSystem

universe u v w

variable {R : Type u} [CommRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (tM : (n : ℕ) → M (n + 1) →ₗ[R] M n)

/-- The composite of the original successive transition maps. -/
def stageTransition {m l : ℕ} (hml : m ≤ l) : M l →ₗ[R] M m :=
  (Functor.OfSequence.map (fun n => (ModuleCat.ofHom (tM n)).op) m l hml).unop.hom

theorem stageTransition_refl (m : ℕ) :
    stageTransition M tM (le_refl m) = LinearMap.id :=
  congrArg (fun a : op (ModuleCat.of R (M m)) ⟶ op (ModuleCat.of R (M m)) =>
    a.unop.hom) (Functor.OfSequence.map_id (fun n => (ModuleCat.ofHom (tM n)).op) m)

/-- At adjacent stages the composite is the supplied map itself. -/
theorem stageTransition_succ (m : ℕ) :
    stageTransition M tM (Nat.le_succ m) = tM m :=
  congrArg (fun a : op (ModuleCat.of R (M m)) ⟶ op (ModuleCat.of R (M (m + 1))) =>
    a.unop.hom) (Functor.OfSequence.map_le_succ (fun n => (ModuleCat.ofHom (tM n)).op) m)

/-- Multistage transitions use their original order of composition. -/
theorem stageTransition_comp {m l k : ℕ} (hml : m ≤ l) (hlk : l ≤ k) :
    stageTransition M tM (hml.trans hlk) =
      (stageTransition M tM hml).comp (stageTransition M tM hlk) :=
  congrArg (fun a : op (ModuleCat.of R (M m)) ⟶ op (ModuleCat.of R (M k)) =>
    a.unop.hom) (Functor.OfSequence.map_comp
      (fun n => (ModuleCat.ofHom (tM n)).op) m l k hml hlk)

/-- Every actual compatible sequence respects the full composite transition. -/
theorem stageTransition_eval {m l : ℕ} (hml : m ≤ l) (x : sections M tM) :
    stageTransition M tM hml (eval M tM l x) = eval M tM m x := by
  induction l, hml using Nat.le_induction with
  | base =>
      rw [stageTransition_refl]
      rfl
  | succ l hml ih =>
      rw [stageTransition_comp M tM hml (Nat.le_succ l), stageTransition_succ,
        LinearMap.comp_apply, transition_eval, ih]

variable (N : ℕ → Type w) [∀ n : ℕ, AddCommGroup (N n)] [∀ n : ℕ, Module R (N n)]
  (tN : (n : ℕ) → N (n + 1) →ₗ[R] N n)
  (φ : compatibleMaps M tM N tN)

/-- The image of the actual kernel in an original stage of the system. -/
def kernelImage (m : ℕ) : Submodule R (M m) :=
  (sectionsMap M tM N tN φ).ker.map (eval M tM m)

/-- These original-stage images consist of elements killed by the original map. -/
theorem kernelImage_le_ker (m : ℕ) :
    kernelImage M tM N tN φ m ≤ (φ.val m).ker := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  change φ.val m (eval M tM m x) = 0
  rw [← eval_sectionsMap, LinearMap.mem_ker.mp hx, map_zero]

/-- The given transition restricts to the actual kernel images. -/
def kernelImageTransition (m : ℕ) :
    kernelImage M tM N tN φ (m + 1) →ₗ[R] kernelImage M tM N tN φ m :=
  ((tM m).domRestrict (kernelImage M tM N tN φ (m + 1))).codRestrict
    (kernelImage M tM N tN φ m) (by
      intro y
      obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp y.property
      apply Submodule.mem_map.mpr
      refine ⟨x, hx, ?_⟩
      change eval M tM m x = tM m y.val
      rw [← he, transition_eval])

/-- Transition of an actual kernel element retains its original evaluation. -/
theorem kernelImageTransition_eval (m : ℕ) (x : (sectionsMap M tM N tN φ).ker) :
    kernelImageTransition M tM N tN φ m
        ((eval M tM (m + 1)).submoduleMap (sectionsMap M tM N tN φ).ker x) =
      (eval M tM m).submoduleMap (sectionsMap M tM N tN φ).ker x := by
  apply Subtype.ext
  exact transition_eval M tM m x.val

/-- The stable-image transitions are surjective by the same original kernel element. -/
theorem kernelImageTransition_surjective (m : ℕ) :
    Function.Surjective (kernelImageTransition M tM N tN φ m) := by
  intro y
  obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp y.property
  refine ⟨(eval M tM (m + 1)).submoduleMap
    (sectionsMap M tM N tN φ).ker ⟨x, hx⟩, ?_⟩
  rw [kernelImageTransition_eval]
  exact Subtype.ext he

section EffectiveSource

variable (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R]
  [∀ n : ℕ, Module.Finite R (M n)]
  (htM : ∀ n : ℕ, Function.Surjective (tM n))
  (hkerM : ∀ n : ℕ, (tM n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
  (hpowM : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)

include htM hkerM hpowM in
/-- The kernel is finite because its effective source was constructed as a finite module. -/
theorem sectionsMap_kernel_finite : Module.Finite R (sectionsMap M tM N tN φ).ker := by
  have hfinite : Module.Finite R (sections M tM) := finite M tM I htM hkerM hpowM
  infer_instance

/-- The proven quotient comparison identifies the ambient reduced-kernel image
with the image inside the original supplied stage. -/
def kernelImageEquiv (m : ℕ) :
    AdicKernel.imageAt I (sectionsMap M tM N tN φ).ker (m + 1) ≃ₗ[R]
      kernelImage M tM N tN φ m := by
  let e := quotientEquiv M tM I htM hkerM hpowM m
  have he : e.toLinearMap.comp
      (I ^ (m + 1) • (⊤ : Submodule R (sections M tM))).mkQ = eval M tM m := by
    apply LinearMap.ext
    intro x
    exact quotientEquiv_mk M tM I htM hkerM hpowM m x
  refine e.ofSubmodules (AdicKernel.imageAt I (sectionsMap M tM N tN φ).ker (m + 1))
    (kernelImage M tM N tN φ m) ?_
  change ((sectionsMap M tM N tN φ).ker.map
    (I ^ (m + 1) • (⊤ : Submodule R (sections M tM))).mkQ).map e.toLinearMap =
      (sectionsMap M tM N tN φ).ker.map (eval M tM m)
  rw [← Submodule.map_comp, he]

/-- The comparison with the original stage retains the original kernel element. -/
theorem kernelImageEquiv_projection (m : ℕ) (x : (sectionsMap M tM N tN φ).ker) :
    kernelImageEquiv M tM N tN φ I htM hkerM hpowM m
        (AdicKernel.imageProjection I (sectionsMap M tM N tN φ).ker (m + 1) x) =
      (eval M tM m).submoduleMap (sectionsMap M tM N tN φ).ker x := by
  apply Subtype.ext
  exact quotientEquiv_mk M tM I htM hkerM hpowM m x.val

include htM hkerM hpowM in
/-- For every precision, sufficiently late stable images recover the actual
kernel's intrinsic adic quotient. The isomorphism is induced by evaluation. -/
theorem exists_kernelImage_quotient_equiv :
    let K : Submodule R (sections M tM) := (sectionsMap M tM N tN φ).ker
    let _qK : HasQuotient K (Submodule R K) := Submodule.hasQuotient (R := R) (M := K)
    ∃ c : ℕ, ∀ (n m : ℕ), n + c ≤ m + 1 →
      ∃ e :
        (K ⧸ (I ^ n • (⊤ : Submodule R K))) ≃ₗ[R]
        (kernelImage M tM N tN φ m ⧸
          (I ^ n • (⊤ : Submodule R (kernelImage M tM N tN φ m)))),
        ∀ x : K,
          e (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk ((eval M tM m).submoduleMap K x) := by
  intro K _qK
  have hfinite : Module.Finite R (sections M tM) := finite M tM I htM hkerM hpowM
  refine ⟨AdicKernel.imageBound I K, ?_⟩
  intro n m hm
  let b := kernelImageEquiv M tM N tN φ I htM hkerM hpowM m
  have hb : (I ^ n • (⊤ : Submodule R (AdicKernel.imageAt I K (m + 1)))).map
      b.toLinearMap = I ^ n • (⊤ : Submodule R (kernelImage M tM N tN φ m)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr b.surjective]
  let eb := Submodule.Quotient.equiv
    (I ^ n • (⊤ : Submodule R (AdicKernel.imageAt I K (m + 1))))
    (I ^ n • (⊤ : Submodule R (kernelImage M tM N tN φ m))) b hb
  let e := ((AdicKernel.imageQuotientEquiv I K n (m + 1) hm).restrictScalars R).trans eb
  refine ⟨e, ?_⟩
  intro x
  change eb (AdicKernel.imageQuotientEquiv I K n (m + 1) hm (Submodule.Quotient.mk x)) = _
  rw [AdicKernel.imageQuotientEquiv_mk]
  change Submodule.Quotient.mk (b (AdicKernel.imageProjection I K (m + 1) x)) = _
  exact congrArg Submodule.Quotient.mk
    (kernelImageEquiv_projection M tM N tN φ I htM hkerM hpowM m x)

section EffectiveTarget

variable [∀ n : ℕ, Module.Finite R (N n)]
  (htN : ∀ n : ℕ, Function.Surjective (tN n))
  (hkerN : ∀ n : ℕ, (tN n).ker = I ^ (n + 1) • (⊤ : Submodule R (N (n + 1))))
  (hpowN : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (N n)) = ⊥)

include htM hkerM hpowM htN hkerN hpowN in
/-- Images of the original stage kernels eventually equal the image of the
constructed kernel, along the actual composite transition maps. -/
theorem exists_stage_kernel_image_stable :
    ∃ c : ℕ, ∀ (m l : ℕ) (hml : m ≤ l), m + c ≤ l →
      ((φ.val l).ker).map (stageTransition M tM hml) = kernelImage M tM N tN φ m := by
  have hfiniteN : Module.Finite R (sections N tN) := finite N tN I htN hkerN hpowN
  let F : sections M tM →ₗ[R] sections N tN := sectionsMap M tM N tN φ
  obtain ⟨c, hc⟩ := AdicKernel.exists_preimage_bound I F
  refine ⟨c, ?_⟩
  intro m l hml hl
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨x, rfl⟩ := eval_surjective M tM I htM hkerM l z
    have hfx : F x ∈ (eval N tN l).ker := by
      change eval N tN l (sectionsMap M tM N tN φ x) = 0
      rw [eval_sectionsMap]
      exact LinearMap.mem_ker.mp hz
    rw [ker_eval N tN I htN hkerN hpowN l] at hfx
    have hindex : (m + 1) + c ≤ l + 1 := by
      rw [Nat.add_right_comm m 1 c]
      exact Nat.add_le_add_right hl 1
    have hx : x ∈ F.ker ⊔ I ^ (m + 1) • (⊤ : Submodule R (sections M tM)) :=
      hc (m + 1) (Submodule.pow_smul_top_le I (sections N tN) hindex hfx)
    obtain ⟨k, hk, z, hz, hx⟩ := Submodule.mem_sup.mp hx
    have hz0 : eval M tM m z = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_eval M tM I htM hkerM hpowM m]
      exact hz
    apply Submodule.mem_map.mpr
    refine ⟨k, hk, ?_⟩
    rw [stageTransition_eval, ← hx, map_add, hz0, add_zero]
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    apply Submodule.mem_map.mpr
    refine ⟨eval M tM l x, ?_, stageTransition_eval M tM hml x⟩
    change φ.val l (eval M tM l x) = 0
    rw [← eval_sectionsMap, LinearMap.mem_ker.mp hx, map_zero]

end EffectiveTarget

end EffectiveSource

end AdicModuleSystem
