/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModules
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemHom
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemKernel
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientSequence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The actual kernel object of finite adic module systems

The kernel of the map of compatible-sequence modules is an actual finite
module. Its own adic quotients, with their original quotient transitions,
form the kernel system. Evaluation induces its map to the original source
system.

Every compatible family killed by the original map factors uniquely
through this quotient system. Existence descends the literal map into
the constructed kernel. Uniqueness follows by recovering the complete
kernel from its own quotient sequence. The stage kernel itself need not
be the stage of this kernel system.

This supplies the affine universal property in the construction of
https://stacks.math.columbia.edu/tag/087X.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w a

variable {R : Type u} [CommRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (tM : (n : ℕ) → M (n + 1) →ₗ[R] M n)
  (N : ℕ → Type w) [∀ n : ℕ, AddCommGroup (N n)] [∀ n : ℕ, Module R (N n)]
  (tN : (n : ℕ) → N (n + 1) →ₗ[R] N n)
  (φ : compatibleMaps M tM N tN)

/-- The actual kernel retained as a native module object. -/
def kernelModule : ModuleCat.{v} R :=
  ModuleCat.of R (sectionsMap M tM N tN φ).ker

/-- Its original inclusion in the module of compatible source sequences. -/
def kernelModuleι : kernelModule M tM N tN φ →ₗ[R] sections M tM :=
  (sectionsMap M tM N tN φ).ker.subtype

variable (I : Ideal R)
  (hpowM : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)

/-- Evaluation induces the kernel quotient's map to the original finite stage. -/
def kernelQuotientInclusion (n : ℕ) :
    quotientSequenceModule I (kernelModule M tM N tN φ) n →ₗ[R] M n :=
  (I ^ (n + 1) • (⊤ : Submodule R (kernelModule M tM N tN φ))).liftQ
    ((eval M tM n).comp (kernelModuleι M tM N tN φ)) (by
      intro x hx
      have hmem : ((eval M tM n).comp (kernelModuleι M tM N tN φ)) x ∈
          I ^ (n + 1) • (⊤ : Submodule R (M n)) :=
        Submodule.smul_top_le_comap_smul_top (I ^ (n + 1))
          ((eval M tM n).comp (kernelModuleι M tM N tN φ)) hx
      rw [hpowM n] at hmem
      exact LinearMap.mem_ker.mpr hmem)

/-- The kernel quotient map is induced by the literal original evaluation. -/
theorem kernelQuotientInclusion_mk (n : ℕ) (x : kernelModule M tM N tN φ) :
    kernelQuotientInclusion M tM N tN φ I hpowM n (Submodule.Quotient.mk x) =
      eval M tM n (kernelModuleι M tM N tN φ x) := rfl

/-- These original evaluation maps commute with the original transitions. -/
def kernelQuotientInclusions : compatibleMaps
    (fun n => quotientSequenceModule I (kernelModule M tM N tN φ) n)
    (quotientSequenceTransition I (kernelModule M tM N tN φ)) M tM :=
  ⟨kernelQuotientInclusion M tM N tN φ I hpowM, by
    intro n x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
      (I ^ ((n + 1) + 1) • (⊤ : Submodule R (kernelModule M tM N tN φ))) x
    exact transition_eval M tM n (kernelModuleι M tM N tN φ y)⟩

/-- The original family vanishes on the actual kernel quotient system. -/
theorem kernelQuotientInclusion_comp (n : ℕ) :
    (φ.val n).comp (kernelQuotientInclusion M tM N tN φ I hpowM n) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
    (I ^ (n + 1) • (⊤ : Submodule R (kernelModule M tM N tN φ))) x
  change φ.val n (eval M tM n (kernelModuleι M tM N tN φ y)) = 0
  rw [← eval_sectionsMap]
  have hy : sectionsMap M tM N tN φ (kernelModuleι M tM N tN φ y) = 0 :=
    LinearMap.map_coe_ker (sectionsMap M tM N tN φ) y
  rw [hy, map_zero]

section Effective

variable [IsNoetherianRing R] [IsAdicComplete I R]
  [∀ n : ℕ, Module.Finite R (M n)]
  (htM : ∀ n : ℕ, Function.Surjective (tM n))
  (hkerM : ∀ n : ℕ, (tM n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))

include htM hkerM hpowM in
/-- The actual kernel quotient stages are finite, with no finite kernel
or effective kernel supplied as input. -/
theorem kernelQuotientModule_finite (n : ℕ) :
    Module.Finite R (quotientSequenceModule I (kernelModule M tM N tN φ) n) := by
  have hfinite : Module.Finite R (kernelModule M tM N tN φ) :=
    sectionsMap_kernel_finite M tM N tN φ I htM hkerM hpowM
  have hquotient := Module.Finite.quotient R
    (I ^ (n + 1) • (⊤ : Submodule R (kernelModule M tM N tN φ)))
  exact hquotient

variable (P : ℕ → Type a) [∀ n : ℕ, AddCommGroup (P n)] [∀ n : ℕ, Module R (P n)]
  (tP : (n : ℕ) → P (n + 1) →ₗ[R] P n)
  [∀ n : ℕ, Module.Finite R (P n)]
  (htP : ∀ n : ℕ, Function.Surjective (tP n))
  (hkerP : ∀ n : ℕ, (tP n).ker = I ^ (n + 1) • (⊤ : Submodule R (P (n + 1))))
  (hpowP : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (P n)) = ⊥)

include htM hkerM htP hkerP hpowP in
/-- Every compatible family killed by the original map factors uniquely
through the constructed kernel's own adic quotient system. -/
theorem existsUnique_kernelQuotient_factor (g : compatibleMaps P tP M tM)
    (hg : ∀ n : ℕ, (φ.val n).comp (g.val n) = 0) :
    ∃! h : compatibleMaps P tP
      (fun n => quotientSequenceModule I (kernelModule M tM N tN φ) n)
      (quotientSequenceTransition I (kernelModule M tM N tN φ)),
      ∀ n : ℕ, (kernelQuotientInclusion M tM N tN φ I hpowM n).comp (h.val n) =
        g.val n := by
  let K : ModuleCat.{v} R := kernelModule M tM N tN φ
  let Q : ℕ → ModuleCat.{v} R := fun n => quotientSequenceModule I K n
  let tQ : (n : ℕ) → Q (n + 1) →ₗ[R] Q n := quotientSequenceTransition I K
  let κ : K →ₗ[R] sections M tM := kernelModuleι M tM N tN φ
  have hfinite : Module.Finite R K :=
    sectionsMap_kernel_finite M tM N tN φ I htM hkerM hpowM
  have hcomplete : IsAdicComplete I K := IsAdicComplete.of_module_finite I K
  let e : K ≃ₗ[R] sections (fun n => Q n) tQ := quotientSequenceEquiv I K
  let G : sections P tP →ₗ[R] sections M tM := sectionsMap P tP M tM g
  have hG : ∀ x : sections P tP, G x ∈ (sectionsMap M tM N tN φ).ker := by
    intro x
    change sectionsMap M tM N tN φ (G x) = 0
    apply Subtype.ext
    funext n
    exact LinearMap.congr_fun (hg n) (eval P tP n x)
  let L : sections P tP →ₗ[R] K := G.codRestrict (sectionsMap M tM N tN φ).ker hG
  let F : sections P tP →ₗ[R] sections (fun n => Q n) tQ := e.toLinearMap.comp L
  let qpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (Q n)) = ⊥ :=
    quotientSequenceModule_annihilated I K
  let h : compatibleMaps P tP (fun n => Q n) tQ :=
    stageMaps P tP (fun n => Q n) tQ I htP hkerP hpowP qpow F
  have heval (n : ℕ) (x : sections P tP) :
      h.val n (eval P tP n x) = Submodule.Quotient.mk (L x) :=
    (stageMap_eval P tP (fun n => Q n) tQ I htP hkerP hpowP qpow F n x).trans
      (quotientSequenceEquiv_eval I K n (L x))
  refine ⟨h, ?_, ?_⟩
  · intro n
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := eval_surjective P tP I htP hkerP n x
    change kernelQuotientInclusion M tM N tN φ I hpowM n
      (h.val n (eval P tP n y)) = g.val n (eval P tP n y)
    rw [heval, kernelQuotientInclusion_mk]
    exact eval_sectionsMap P tP M tM g n y
  · intro h' hh'
    apply (homEquiv P tP (fun n => Q n) tQ I htP hkerP hpowP qpow).injective
    apply LinearMap.ext
    intro x
    apply e.symm.injective
    have hκ : Function.Injective κ := Subtype.val_injective
    apply hκ
    have hleft : κ (e.symm (sectionsMap P tP (fun n => Q n) tQ h' x)) = G x := by
      apply Subtype.ext
      funext n
      have hclass :
          (Submodule.Quotient.mk (e.symm (sectionsMap P tP (fun n => Q n) tQ h' x)) :
            Q n) = h'.val n (eval P tP n x) :=
        quotientSequenceEquiv_symm_mk I K n
          (sectionsMap P tP (fun n => Q n) tQ h' x)
      have hfac := LinearMap.congr_fun (hh' n) (eval P tP n x)
      calc
        eval M tM n (κ (e.symm (sectionsMap P tP (fun n => Q n) tQ h' x))) =
            kernelQuotientInclusion M tM N tN φ I hpowM n
              (Submodule.Quotient.mk (e.symm
                (sectionsMap P tP (fun n => Q n) tQ h' x))) :=
          (kernelQuotientInclusion_mk M tM N tN φ I hpowM n _).symm
        _ = kernelQuotientInclusion M tM N tN φ I hpowM n
            (h'.val n (eval P tP n x)) :=
          congrArg (kernelQuotientInclusion M tM N tN φ I hpowM n) hclass
        _ = g.val n (eval P tP n x) := hfac
        _ = eval M tM n (G x) := (eval_sectionsMap P tP M tM g n x).symm
    have hright : κ (e.symm (sectionsMap P tP (fun n => Q n) tQ h x)) = G x := by
      have hmap := LinearMap.congr_fun
        (sectionsMap_stageMaps P tP (fun n => Q n) tQ I htP hkerP hpowP qpow F) x
      change κ (e.symm (sectionsMap P tP (fun n => Q n) tQ h x)) = G x
      rw [hmap]
      change κ (e.symm (e (L x))) = G x
      rw [e.symm_apply_apply]
      rfl
    exact hleft.trans hright.symm

end Effective

end AdicModuleSystem
