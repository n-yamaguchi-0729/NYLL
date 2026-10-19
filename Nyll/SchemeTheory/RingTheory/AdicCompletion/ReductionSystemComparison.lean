/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemOverCompletion
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Operations

/-!
# Completion of an actual reduction system

Given compatible maps from a module to its successive reductions, complete
these same maps and assemble their values into compatible sections. If the
original maps are surjective with kernels given by the corresponding ideal
powers, the resulting map is bijective over the completed coefficient ring.

The proof derives the transition kernels and stage annihilation from the
original maps. Completeness supplies surjectivity, while the original kernel
equalities detect every coordinate of the source completion.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)
  {P : Type v} [AddCommGroup P] [Module R P]

private theorem reduction_stage_annihilation
    {N : Type w} [AddCommGroup N] [Module R N]
    (η : P →ₗ[R] N) (n : ℕ) (hηsurj : Function.Surjective η)
    (hηker : η.ker = I ^ n • (⊤ : Submodule R P)) :
    I ^ n • (⊤ : Submodule R N) = ⊥ := by
  have h : η.ker.map η = ⊥ := LinearMap.le_ker_iff_map.mp le_rfl
  rw [hηker, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr hηsurj] at h
  exact h

private theorem reduceModIdeal_injective_of_kernel
    {N : Type w} [AddCommGroup N] [Module R N]
    (η : P →ₗ[R] N) (n : ℕ) (hηsurj : Function.Surjective η)
    (hηker : η.ker = I ^ n • (⊤ : Submodule R P)) :
    Function.Injective (η.reduceModIdeal (I ^ n)) := by
  have hpow : I ^ n • (⊤ : Submodule R N) = ⊥ :=
    reduction_stage_annihilation I η n hηsurj hηker
  intro a b hab
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • (⊤ : Submodule R P)) a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • (⊤ : Submodule R P)) b
  have hab' : (Submodule.Quotient.mk (η x) : N ⧸
      (I ^ n • (⊤ : Submodule R N))) = Submodule.Quotient.mk (η y) := hab
  have hmem : η x - η y ∈ I ^ n • (⊤ : Submodule R N) :=
    (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule R N))).mp hab'
  rw [hpow, Submodule.mem_bot] at hmem
  have hz : η (x - y) = 0 := (η.map_sub x y).trans hmem
  apply (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule R P))).mpr
  rw [← hηker]
  exact LinearMap.mem_ker.mpr hz

variable (Q : ℕ → Type w)
  [∀ n : ℕ, AddCommGroup (Q n)] [∀ n : ℕ, Module R (Q n)]
  (δ : ∀ n : ℕ, Q (n + 1) →ₗ[R] Q n)
  (η : ∀ n : ℕ, P →ₗ[R] Q n)
  (hη : ∀ n : ℕ, (δ n).comp (η (n + 1)) = η n)

/-- Complete the original reduction maps, retaining their literal components. -/
def completedReductionSectionsMap :
    AdicCompletion I P →ₗ[AdicCompletion I R]
      sections (fun n => AdicCompletion I (Q n))
        (fun n => AdicCompletion.map I (δ n)) where
  toFun x := ⟨fun n => AdicCompletion.map I (η n) x, by
    intro n
    exact (AdicCompletion.map_comp_apply I (η (n + 1)) (δ n) x).trans
      (congrArg (fun a : P →ₗ[R] Q n => AdicCompletion.map I a x) (hη n))⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (AdicCompletion.map I (η n)).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact (AdicCompletion.map I (η n)).map_smul r x

/-- Each coordinate is the completion of the prescribed original reduction. -/
theorem completedReductionSectionsMap_apply (x : AdicCompletion I P) (n : ℕ) :
    (completedReductionSectionsMap I Q δ η hη x).val n = AdicCompletion.map I (η n) x :=
  rfl

include hη in
private theorem reduction_transition_kernel
    (hηsurj : ∀ n : ℕ, Function.Surjective (η n))
    (hηker : ∀ n : ℕ, (η n).ker = I ^ (n + 1) • (⊤ : Submodule R P)) (n : ℕ) :
    (δ n).ker = I ^ (n + 1) • (⊤ : Submodule R (Q (n + 1))) := by
  have h : ((δ n).ker).comap (η (n + 1)) = (η n).ker :=
    (LinearMap.ker_comp (η (n + 1)) (δ n)).symm.trans
      (congrArg LinearMap.ker (hη n))
  have hmap := congrArg (Submodule.map (η (n + 1))) h
  rw [Submodule.map_comap_eq_of_surjective (hηsurj (n + 1)), hηker n,
    Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (hηsurj (n + 1))] at hmap
  exact hmap

/-- The original reduction kernels determine every coordinate of the completion. -/
theorem completedReductionSectionsMap_injective
    (hηsurj : ∀ n : ℕ, Function.Surjective (η n))
    (hηker : ∀ n : ℕ, (η n).ker = I ^ (n + 1) • (⊤ : Submodule R P)) :
    Function.Injective (completedReductionSectionsMap I Q δ η hη) := by
  intro x y hxy
  apply AdicCompletion.ext
  intro n
  have hstage : AdicCompletion.map I (η n) x = AdicCompletion.map I (η n) y :=
    congrArg (fun z : sections (fun k => AdicCompletion I (Q k))
      (fun k => AdicCompletion.map I (δ k)) => z.val n) hxy
  have hcoord : (η n).reduceModIdeal (I ^ (n + 1)) (x.val (n + 1)) =
      (η n).reduceModIdeal (I ^ (n + 1)) (y.val (n + 1)) :=
    congrArg (fun z : AdicCompletion I (Q n) => z.val (n + 1)) hstage
  have hpos : x.val (n + 1) = y.val (n + 1) :=
    reduceModIdeal_injective_of_kernel I (η n) (n + 1) (hηsurj n) (hηker n) hcoord
  exact (x.property (Nat.le_succ n)).symm.trans
    ((congrArg (AdicCompletion.transitionMap I P (Nat.le_succ n)) hpos).trans
      (y.property (Nat.le_succ n)))

/-- Compatible completed reductions lift to the original module completion. -/
theorem completedReductionSectionsMap_surjective
    (hηsurj : ∀ n : ℕ, Function.Surjective (η n))
    (hηker : ∀ n : ℕ, (η n).ker = I ^ (n + 1) • (⊤ : Submodule R P)) (hfg : I.FG) :
    Function.Surjective (completedReductionSectionsMap I Q δ η hη) := by
  have hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (Q n)) = ⊥ :=
    fun n => reduction_stage_annihilation I (η n) (n + 1) (hηsurj n) (hηker n)
  have hker : ∀ n : ℕ, (δ n).ker = I ^ (n + 1) • (⊤ : Submodule R (Q (n + 1))) :=
    reduction_transition_kernel I Q δ η hη hηsurj hηker
  have hcomplete : IsAdicComplete I (AdicCompletion I P) :=
    AdicCompletion.isAdicComplete (I := I) (M := P) hfg
  have : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R)))
      (AdicCompletion I P) :=
    (IsAdicComplete.map_algebraMap_iff (I := I)
      (S := AdicCompletion I R) (M := AdicCompletion I P)).mpr hcomplete
  exact surjective_of_surjective_components
    (fun n => AdicCompletion I (Q n)) (fun n => AdicCompletion.map I (δ n))
    (I.map (algebraMap R (AdicCompletion I R)))
    (completed_transition_kernel Q δ I hpow hker)
    (completed_stage_annihilation Q I hpow)
    (completedReductionSectionsMap I Q δ η hη)
    (fun n => AdicCompletion.map_surjective I (hηsurj n))

/-- The actual reduction maps induce a bijective map over the completed coefficient ring. -/
theorem completedReductionSectionsMap_bijective
    (hηsurj : ∀ n : ℕ, Function.Surjective (η n))
    (hηker : ∀ n : ℕ, (η n).ker = I ^ (n + 1) • (⊤ : Submodule R P)) (hfg : I.FG) :
    Function.Bijective (completedReductionSectionsMap I Q δ η hη) :=
  ⟨completedReductionSectionsMap_injective I Q δ η hη hηsurj hηker,
    completedReductionSectionsMap_surjective I Q δ η hη hηsurj hηker hfg⟩

end AdicModuleSystem
