/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionLocalRing
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual coefficient quotients of an adic completion

Evaluation identifies the quotient of the completed ring by the extended
ideal power with the original ideal-power quotient. The comparison is an
algebra equivalence over the original ring and retains literal evaluation.
In particular, every completed quotient coefficient has an original-ring
representative. No local-ring hypothesis is used.
-/

noncomputable section

namespace AdicCompletion

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)

/-- Evaluation gives the actual quotient-ring comparison, with its
original coefficient algebra structure. -/
def quotientPowAlgEquiv (n : ℕ) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃ₐ[R]
      R ⧸ I ^ n := by
  have hker : RingHom.ker (evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n :=
    (ker_evalₐ_eq_map_pow I hI n).trans (Ideal.map_pow (algebraMap R (AdicCompletion I R)) I n)
  exact (Ideal.quotientEquivAlgOfEq R hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

/-- The class of an actual completed coefficient is its original evaluation. -/
theorem quotientPowAlgEquiv_mk (n : ℕ) (x : AdicCompletion I R) :
    quotientPowAlgEquiv I hI n (Ideal.Quotient.mk _ x) = evalₐ I n x := by
  have hker : RingHom.ker (evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n :=
    (ker_evalₐ_eq_map_pow I hI n).trans
      (Ideal.map_pow (algebraMap R (AdicCompletion I R)) I n)
  let e := Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n)
  have h₁ := Ideal.quotientEquivAlgOfEq_mk R hker.symm x
  have h₂ := Ideal.quotientKerAlgEquivOfSurjective_mk (surjective_evalₐ I n) x
  exact (congrArg e h₁).trans h₂

include hI in
/-- Every completed quotient coefficient is represented by an element
of the original ring, through its actual algebra map. -/
theorem algebraMap_quotientPow_surjective (n : ℕ) :
    Function.Surjective
      (algebraMap R
        (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n)) := by
  intro x
  let e := quotientPowAlgEquiv I hI n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e x)
  refine ⟨r, e.injective ?_⟩
  exact (e.commutes r).trans hr

end AdicCompletion
