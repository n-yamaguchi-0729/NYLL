/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The actual sequence of adic quotients of a module

The stages are the original quotients by `I ^ (n + 1)`, retained as native
module objects. Their transition maps are the native quotient maps. Their
kernels and annihilating ideal powers are computed directly.

For a complete module, the module of compatible sequences of these stages
is linearly equivalent to the original module. The inverse is constructed
by the completeness lifting theorem for the strictly increasing sequence
`n + 1`, and every quotient class is preserved.
-/

noncomputable section

namespace AdicModuleSystem

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)
  (M : Type v) [AddCommGroup M] [Module R M]

/-- The original quotient at the positive adic degree `n + 1`. -/
def quotientSequenceModule (n : ℕ) : ModuleCat.{v} R :=
  ModuleCat.of R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))

/-- The original quotient transition between adjacent positive degrees. -/
def quotientSequenceTransition (n : ℕ) :
    quotientSequenceModule I M (n + 1) →ₗ[R] quotientSequenceModule I M n :=
  Submodule.factorPow I M (Nat.le_succ (n + 1))

/-- Every quotient transition is surjective. -/
theorem quotientSequenceTransition_surjective (n : ℕ) :
    Function.Surjective (quotientSequenceTransition I M n) :=
  Submodule.factor_surjective (Submodule.pow_smul_top_le I M (Nat.le_succ (n + 1)))

/-- The transition kernel is the actual extended ideal power in the later stage. -/
theorem quotientSequenceTransition_ker (n : ℕ) :
    (quotientSequenceTransition I M n).ker =
      I ^ (n + 1) • (⊤ : Submodule R (quotientSequenceModule I M (n + 1))) := by
  have h := Submodule.ker_mapQ
    (I ^ ((n + 1) + 1) • (⊤ : Submodule R M))
    (I ^ (n + 1) • (⊤ : Submodule R M)) (LinearMap.id : M →ₗ[R] M)
    (Submodule.pow_smul_top_le I M (Nat.le_succ (n + 1)))
  rw [Submodule.comap_id, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h
  exact h

/-- Each original quotient is annihilated by its defining ideal power. -/
theorem quotientSequenceModule_annihilated (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (quotientSequenceModule I M n)) = ⊥ := by
  have h := Submodule.mkQ_map_self (I ^ (n + 1) • (⊤ : Submodule R M))
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h
  exact h

/-- An original element gives its actual compatible family of quotient classes. -/
def quotientSequence :
    M →ₗ[R] sections (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) where
  toFun x := ⟨fun n => Submodule.Quotient.mk x, fun _ => rfl⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ.map_add x y
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ.map_smul r x

/-- Evaluation of the original sequence is the original quotient class. -/
theorem quotientSequence_eval (n : ℕ) (x : M) :
    eval (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) n
        (quotientSequence I M x) = Submodule.Quotient.mk x := rfl

section Complete

variable [IsAdicComplete I M]

/-- Completeness recovers an original element from its positive-degree classes. -/
def quotientSequenceLimit :
    sections (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) →ₗ[R] M :=
  IsAdicComplete.StrictMono.lift I (strictMono_id.add_const 1)
    (fun n => eval (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) n)
    (by
      intro n
      apply LinearMap.ext
      intro x
      exact transition_eval (fun n => quotientSequenceModule I M n)
        (quotientSequenceTransition I M) n x)

/-- The recovered element represents every supplied quotient class. -/
theorem quotientSequenceLimit_mk (n : ℕ)
    (x : sections (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M)) :
    (Submodule.Quotient.mk (quotientSequenceLimit I M x) : quotientSequenceModule I M n) =
      eval (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) n x :=
  IsAdicComplete.StrictMono.mk_lift I (strictMono_id.add_const 1)
    (fun k => eval (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) k)
    (by
      intro k
      apply LinearMap.ext
      intro y
      exact transition_eval (fun n => quotientSequenceModule I M n)
        (quotientSequenceTransition I M) k y) x

/-- The actual compatible quotient family is equivalent to the complete original module. -/
def quotientSequenceEquiv :
    M ≃ₗ[R] sections (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) :=
  { quotientSequence I M with
    invFun := quotientSequenceLimit I M
    left_inv := by
      intro x
      have h : (fun y : M => quotientSequenceLimit I M (quotientSequence I M y)) =
          fun y : M => y := by
        apply IsHausdorff.StrictMono.funext I (strictMono_id.add_const 1)
        intro n y
        exact quotientSequenceLimit_mk I M n (quotientSequence I M y)
      exact congrFun h x
    right_inv := by
      intro x
      apply Subtype.ext
      funext n
      exact quotientSequenceLimit_mk I M n x }

/-- The equivalence still evaluates to the literal original quotient class. -/
theorem quotientSequenceEquiv_eval (n : ℕ) (x : M) :
    eval (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) n
        (quotientSequenceEquiv I M x) = Submodule.Quotient.mk x :=
  quotientSequence_eval I M n x

/-- The inverse comparison recovers exactly the original stage data. -/
theorem quotientSequenceEquiv_symm_mk (n : ℕ)
    (x : sections (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M)) :
    (Submodule.Quotient.mk ((quotientSequenceEquiv I M).symm x) : quotientSequenceModule I M n) =
      eval (fun n => quotientSequenceModule I M n) (quotientSequenceTransition I M) n x :=
  quotientSequenceLimit_mk I M n x

end Complete

end AdicModuleSystem
