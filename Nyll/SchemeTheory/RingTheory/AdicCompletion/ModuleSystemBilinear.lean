/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Bilinear maps of effective adic systems

Bilinear maps of compatible systems lift by acting on actual sequences.
In the opposite direction, a bilinear map of effective modules descends in
both variables to the computed quotients. This recovers the original stage
maps and proves that multiplication maps and their identities can be checked
at the finite levels.

The source modules are constructed by finite adic effectivity; quotient
identifications, maps on quotients, and their compatibility are all proved.
The target system only needs the specified annihilating ideal powers.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w a

variable {R : Type u} [CommRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (tM : (n : ℕ) → M (n + 1) →ₗ[R] M n)
  (N : ℕ → Type w) [∀ n : ℕ, AddCommGroup (N n)] [∀ n : ℕ, Module R (N n)]
  (tN : (n : ℕ) → N (n + 1) →ₗ[R] N n)
  (P : ℕ → Type a) [∀ n : ℕ, AddCommGroup (P n)] [∀ n : ℕ, Module R (P n)]
  (tP : (n : ℕ) → P (n + 1) →ₗ[R] P n)

/-- Bilinear maps commuting with all three original transition maps. -/
def compatibleBilinearMaps : Submodule R ((n : ℕ) → M n →ₗ[R] N n →ₗ[R] P n) where
  carrier := {f | ∀ (n : ℕ) (x : M (n + 1)) (y : N (n + 1)),
    tP n (f (n + 1) x y) = f n (tM n x) (tN n y)}
  zero_mem' := by
    intro n x y
    exact (tP n).map_zero
  add_mem' := by
    intro f g hf hg n x y
    change tP n (f (n + 1) x y + g (n + 1) x y) =
      f n (tM n x) (tN n y) + g n (tM n x) (tN n y)
    rw [map_add, hf n x y, hg n x y]
  smul_mem' := by
    intro r f hf n x y
    change tP n (r • f (n + 1) x y) = r • f n (tM n x) (tN n y)
    rw [map_smul, hf n x y]

/-- The actual bilinear map on compatible sequences. -/
def sectionsBilinearMap (f : compatibleBilinearMaps M tM N tN P tP) :
    sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP :=
  LinearMap.mk₂ R
    (fun x y => ⟨fun n => f.val n (x.val n) (y.val n), by
      intro n
      rw [f.property n (x.val (n + 1)) (y.val (n + 1)), x.property n, y.property n]⟩)
    (by
      intro x z y
      apply Subtype.ext
      funext n
      exact (f.val n).map_add₂ (x.val n) (z.val n) (y.val n))
    (by
      intro r x y
      apply Subtype.ext
      funext n
      exact (f.val n).map_smul₂ r (x.val n) (y.val n))
    (by
      intro x y z
      apply Subtype.ext
      funext n
      exact (f.val n (x.val n)).map_add (y.val n) (z.val n))
    (by
      intro r x y
      apply Subtype.ext
      funext n
      exact (f.val n (x.val n)).map_smul r (y.val n))

/-- Evaluation recovers the given bilinear map at the specified stage. -/
theorem eval_sectionsBilinearMap (f : compatibleBilinearMaps M tM N tN P tP)
    (n : ℕ) (x : sections M tM) (y : sections N tN) :
    eval P tP n (sectionsBilinearMap M tM N tN P tP f x y) =
      f.val n (eval M tM n x) (eval N tN n y) := rfl

variable (I : Ideal R)
  (hpowP : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (P n)) = ⊥)

private def quotientStageBilinear
    (F : sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP) (n : ℕ) :
    (sections M tM ⧸ (I ^ (n + 1) • (⊤ : Submodule R (sections M tM)))) →ₗ[R]
      (sections N tN ⧸ (I ^ (n + 1) • (⊤ : Submodule R (sections N tN)))) →ₗ[R] P n :=
  (F.compr₂ (eval P tP n)).liftQ₂
    (I ^ (n + 1) • (⊤ : Submodule R (sections M tM)))
    (I ^ (n + 1) • (⊤ : Submodule R (sections N tN)))
    (by
      intro x hx
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      change eval P tP n (F x y) = 0
      have hmem : eval P tP n (F x y) ∈ I ^ (n + 1) • (⊤ : Submodule R (P n)) :=
        Submodule.smul_top_le_comap_smul_top (I ^ (n + 1))
          ((eval P tP n).comp (F.flip y)) hx
      rw [hpowP n] at hmem
      exact hmem)
    (by
      intro y hy
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro x
      change eval P tP n (F x y) = 0
      have hmem : eval P tP n (F x y) ∈ I ^ (n + 1) • (⊤ : Submodule R (P n)) :=
        Submodule.smul_top_le_comap_smul_top (I ^ (n + 1))
          ((eval P tP n).comp (F x)) hy
      rw [hpowP n] at hmem
      exact hmem)

private theorem quotientStageBilinear_mk
    (F : sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP)
    (n : ℕ) (x : sections M tM) (y : sections N tN) :
    quotientStageBilinear M tM N tN P tP I hpowP F n
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = eval P tP n (F x y) := by
  rw [quotientStageBilinear, LinearMap.liftQ₂_mk, LinearMap.compr₂_apply]

section EffectiveSources

variable [IsNoetherianRing R] [IsAdicComplete I R]
  [∀ n : ℕ, Module.Finite R (M n)] [∀ n : ℕ, Module.Finite R (N n)]
  (htM : ∀ n : ℕ, Function.Surjective (tM n))
  (hkerM : ∀ n : ℕ, (tM n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
  (hpowM : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
  (htN : ∀ n : ℕ, Function.Surjective (tN n))
  (hkerN : ∀ n : ℕ, (tN n).ker = I ^ (n + 1) • (⊤ : Submodule R (N (n + 1))))
  (hpowN : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (N n)) = ⊥)

/-- A bilinear map of the effective modules descends in both variables
to the original stages, using their computed quotient identifications. -/
def stageBilinearMap
    (F : sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP) (n : ℕ) :
    M n →ₗ[R] N n →ₗ[R] P n :=
  (quotientStageBilinear M tM N tN P tP I hpowP F n).compl₁₂
    (quotientEquiv M tM I htM hkerM hpowM n).symm.toLinearMap
    (quotientEquiv N tN I htN hkerN hpowN n).symm.toLinearMap

/-- Both quotient identifications preserve evaluation of the original sequences. -/
theorem stageBilinearMap_eval
    (F : sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP)
    (n : ℕ) (x : sections M tM) (y : sections N tN) :
    stageBilinearMap M tM N tN P tP I hpowP htM hkerM hpowM htN hkerN hpowN F n
      (eval M tM n x) (eval N tN n y) = eval P tP n (F x y) := by
  rw [← quotientEquiv_mk M tM I htM hkerM hpowM n x,
    ← quotientEquiv_mk N tN I htN hkerN hpowN n y]
  simp only [stageBilinearMap, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, quotientStageBilinear_mk]

/-- Descending a bilinear map gives a family compatible with the original
transition maps in both arguments and in the result. -/
def stageBilinearMaps
    (F : sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP) :
    compatibleBilinearMaps M tM N tN P tP :=
  ⟨stageBilinearMap M tM N tN P tP I hpowP htM hkerM hpowM htN hkerN hpowN F, by
    intro n x y
    obtain ⟨a, rfl⟩ := eval_surjective M tM I htM hkerM (n + 1) x
    obtain ⟨b, rfl⟩ := eval_surjective N tN I htN hkerN (n + 1) y
    rw [stageBilinearMap_eval, transition_eval P tP, transition_eval M tM,
      transition_eval N tN, stageBilinearMap_eval]⟩

/-- Descending and lifting preserves the original bilinear map. -/
theorem sectionsBilinearMap_stageBilinearMaps
    (F : sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP) :
    sectionsBilinearMap M tM N tN P tP
      (stageBilinearMaps M tM N tN P tP I hpowP htM hkerM hpowM htN hkerN hpowN F) = F := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  funext n
  exact stageBilinearMap_eval M tM N tN P tP I hpowP htM hkerM hpowM htN hkerN hpowN F n x y

/-- Lifting and descending preserves every originally supplied bilinear map. -/
theorem stageBilinearMaps_sectionsBilinearMap
    (f : compatibleBilinearMaps M tM N tN P tP) :
    stageBilinearMaps M tM N tN P tP I hpowP htM hkerM hpowM htN hkerN hpowN
      (sectionsBilinearMap M tM N tN P tP f) = f := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := eval_surjective M tM I htM hkerM n x
  obtain ⟨b, rfl⟩ := eval_surjective N tN I htN hkerN n y
  exact (stageBilinearMap_eval M tM N tN P tP I hpowP htM hkerM hpowM htN hkerN hpowN
    (sectionsBilinearMap M tM N tN P tP f) n a b).trans
      (eval_sectionsBilinearMap M tM N tN P tP f n a b)

/-- Bilinear maps of the effective modules are exactly the compatible
bilinear maps of their finite stages. -/
def bilinearHomEquiv :
    compatibleBilinearMaps M tM N tN P tP ≃ₗ[R]
      (sections M tM →ₗ[R] sections N tN →ₗ[R] sections P tP) where
  toFun := sectionsBilinearMap M tM N tN P tP
  invFun := stageBilinearMaps M tM N tN P tP I hpowP htM hkerM hpowM htN hkerN hpowN
  left_inv := stageBilinearMaps_sectionsBilinearMap M tM N tN P tP I hpowP
    htM hkerM hpowM htN hkerN hpowN
  right_inv := sectionsBilinearMap_stageBilinearMaps M tM N tN P tP I hpowP
    htM hkerM hpowM htN hkerN hpowN
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    rfl

end EffectiveSources

end AdicModuleSystem
