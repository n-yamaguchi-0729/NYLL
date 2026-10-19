/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Morphisms of effective adic module systems

A compatible family of linear maps acts on the actual compatible sequences.
Conversely, a linear map between these sequence modules descends to every
stage: linearity preserves ideal powers, and the computed evaluation kernel
identifies the source stage with its actual quotient. These constructions
are inverse, so morphisms, compositions, and identities are recovered along
with the effective objects.

Only the source system needs the finite effectivity hypotheses for this
comparison. The target stages need to be annihilated by the prescribed ideal
powers. No quotient comparison or descended map is an input.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w a

variable {R : Type u} [CommRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (tM : (n : ℕ) → M (n + 1) →ₗ[R] M n)
  (N : ℕ → Type w) [∀ n : ℕ, AddCommGroup (N n)] [∀ n : ℕ, Module R (N n)]
  (tN : (n : ℕ) → N (n + 1) →ₗ[R] N n)

/-- Linear maps at the actual stages, commuting with the given transitions. -/
def compatibleMaps : Submodule R ((n : ℕ) → M n →ₗ[R] N n) where
  carrier := {f | ∀ (n : ℕ) (x : M (n + 1)), tN n (f (n + 1) x) = f n (tM n x)}
  zero_mem' := by
    intro n x
    exact (tN n).map_zero
  add_mem' := by
    intro f g hf hg n x
    change tN n (f (n + 1) x + g (n + 1) x) = f n (tM n x) + g n (tM n x)
    rw [map_add, hf n x, hg n x]
  smul_mem' := by
    intro r f hf n x
    change tN n (r • f (n + 1) x) = r • f n (tM n x)
    rw [map_smul, hf n x]

/-- A compatible family acts on the original sequences, component by component. -/
def sectionsMap (f : compatibleMaps M tM N tN) : sections M tM →ₗ[R] sections N tN where
  toFun x := ⟨fun n => f.val n (x.val n), by
    intro n
    rw [f.property n (x.val (n + 1)), x.property n]⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (f.val n).map_add (x.val n) (y.val n)
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact (f.val n).map_smul r (x.val n)

/-- The lifted map retains the prescribed map on each finite stage. -/
theorem eval_sectionsMap (f : compatibleMaps M tM N tN) (n : ℕ) (x : sections M tM) :
    eval N tN n (sectionsMap M tM N tN f x) = f.val n (eval M tM n x) := rfl

/-- Lifting compatible families is itself linear. -/
def sectionsMapLinear :
    compatibleMaps M tM N tN →ₗ[R] (sections M tM →ₗ[R] sections N tN) where
  toFun := sectionsMap M tM N tN
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    rfl

section EffectiveSource

variable (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R]
  [∀ n : ℕ, Module.Finite R (M n)]
  (htM : ∀ n : ℕ, Function.Surjective (tM n))
  (hkerM : ∀ n : ℕ, (tM n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
  (hpowM : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
  (hpowN : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (N n)) = ⊥)

/-- The stage map descended from a linear map of effective modules.
Its construction uses the proven quotient identification of the source. -/
def stageMap (F : sections M tM →ₗ[R] sections N tN) (n : ℕ) : M n →ₗ[R] N n :=
  ((I ^ (n + 1) • (⊤ : Submodule R (sections M tM))).liftQ
    ((eval N tN n).comp F) (by
      intro x hx
      have hmem : ((eval N tN n).comp F) x ∈ I ^ (n + 1) • (⊤ : Submodule R (N n)) :=
        Submodule.smul_top_le_comap_smul_top (I ^ (n + 1)) ((eval N tN n).comp F) hx
      rw [hpowN n] at hmem
      exact LinearMap.mem_ker.mpr hmem)).comp
        (quotientEquiv M tM I htM hkerM hpowM n).symm.toLinearMap

/-- Descending a map does not change evaluation of actual compatible sequences. -/
theorem stageMap_eval (F : sections M tM →ₗ[R] sections N tN)
    (n : ℕ) (x : sections M tM) :
    stageMap M tM N tN I htM hkerM hpowM hpowN F n (eval M tM n x) =
      eval N tN n (F x) := by
  rw [← quotientEquiv_mk M tM I htM hkerM hpowM n x]
  simp only [stageMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]

/-- The descended stage maps commute with the originally supplied transitions. -/
def stageMaps (F : sections M tM →ₗ[R] sections N tN) : compatibleMaps M tM N tN :=
  ⟨stageMap M tM N tN I htM hkerM hpowM hpowN F, by
    intro n x
    obtain ⟨y, rfl⟩ := eval_surjective M tM I htM hkerM (n + 1) x
    rw [stageMap_eval, transition_eval N tN, transition_eval M tM, stageMap_eval]⟩

/-- Descending and lifting recovers the original map on compatible sequences. -/
theorem sectionsMap_stageMaps (F : sections M tM →ₗ[R] sections N tN) :
    sectionsMap M tM N tN (stageMaps M tM N tN I htM hkerM hpowM hpowN F) = F := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact stageMap_eval M tM N tN I htM hkerM hpowM hpowN F n x

/-- Lifting and descending recovers every map at its original finite stage. -/
theorem stageMaps_sectionsMap (f : compatibleMaps M tM N tN) :
    stageMaps M tM N tN I htM hkerM hpowM hpowN (sectionsMap M tM N tN f) = f := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := eval_surjective M tM I htM hkerM n x
  exact (stageMap_eval M tM N tN I htM hkerM hpowM hpowN
    (sectionsMap M tM N tN f) n y).trans (eval_sectionsMap M tM N tN f n y)

/-- Morphisms between effective adic modules are precisely compatible families
of morphisms of their supplied stages. The forward map acts componentwise. -/
def homEquiv :
    compatibleMaps M tM N tN ≃ₗ[R] (sections M tM →ₗ[R] sections N tN) :=
  { sectionsMapLinear M tM N tN with
    invFun := stageMaps M tM N tN I htM hkerM hpowM hpowN
    left_inv := stageMaps_sectionsMap M tM N tN I htM hkerM hpowM hpowN
    right_inv := sectionsMap_stageMaps M tM N tN I htM hkerM hpowM hpowN }

/-- Equality of linear maps may be checked on the recovered finite stages. -/
theorem stageMap_ext {F G : sections M tM →ₗ[R] sections N tN}
    (h : ∀ n : ℕ, stageMap M tM N tN I htM hkerM hpowM hpowN F n =
      stageMap M tM N tN I htM hkerM hpowM hpowN G n) : F = G := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact (stageMap_eval M tM N tN I htM hkerM hpowM hpowN F n x).symm.trans
    ((LinearMap.congr_fun (h n) (eval M tM n x)).trans
      (stageMap_eval M tM N tN I htM hkerM hpowM hpowN G n x))

end EffectiveSource

section Composition

variable (P : ℕ → Type a) [∀ n : ℕ, AddCommGroup (P n)] [∀ n : ℕ, Module R (P n)]
  (tP : (n : ℕ) → P (n + 1) →ₗ[R] P n)

/-- Composition of the actual compatible families. -/
def compatibleMapsComp (g : compatibleMaps N tN P tP) (f : compatibleMaps M tM N tN) :
    compatibleMaps M tM P tP :=
  ⟨fun n => (g.val n).comp (f.val n), by
    intro n x
    change tP n (g.val (n + 1) (f.val (n + 1) x)) = g.val n (f.val n (tM n x))
    rw [g.property, f.property]⟩

/-- Composition is preserved on actual compatible sequences. -/
theorem sectionsMap_comp (g : compatibleMaps N tN P tP) (f : compatibleMaps M tM N tN) :
    sectionsMap M tM P tP (compatibleMapsComp M tM N tN P tP g f) =
      (sectionsMap N tN P tP g).comp (sectionsMap M tM N tN f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  rfl

end Composition

/-- The identity family of maps of the original stages. -/
def compatibleMapsId : compatibleMaps M tM M tM :=
  ⟨fun n => (LinearMap.id : M n →ₗ[R] M n), fun _ _ => rfl⟩

/-- The identity family acts as the identity on actual compatible sequences. -/
theorem sectionsMap_id :
    sectionsMap M tM M tM (compatibleMapsId M tM) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  rfl

end AdicModuleSystem
