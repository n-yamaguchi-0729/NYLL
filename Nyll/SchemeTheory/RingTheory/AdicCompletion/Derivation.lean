/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.CompletionFromQuotientEquivalences
public import Nyll.SchemeTheory.RingTheory.Derivation.IdealPowers
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Extending derivations to an adic completion

A derivation sends the `(n+1)`st power of every ideal into its `n`th power.
Consequently applying it to a Cauchy sequence after shifting the index by
one gives another Cauchy sequence. This construction descends through the
native map from Cauchy sequences to the adic completion.

The resulting derivation retains the original ring elements and has a
concrete finite-level characterization. No finite generation, noetherianity,
or assumed continuity of the derivation is needed.
-/

@[expose] public section

noncomputable section

namespace Derivation

universe u

variable {R : Type u} [CommRing R] (D : Derivation ℤ R R) (I : Ideal R)

private theorem quotient_derivative_eq (n : ℕ) {a b : R}
    (h : Ideal.Quotient.mk (I ^ (n + 1)) a = Ideal.Quotient.mk (I ^ (n + 1)) b) :
    Ideal.Quotient.mk (I ^ n) (D a) = Ideal.Quotient.mk (I ^ n) (D b) := by
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub D]
  exact D.map_mem_pow_succ I n (Ideal.Quotient.eq.mp h)

/-- Differentiate an adic Cauchy sequence after shifting the ideal-power index by one. -/
def adicSequence (a : AdicCompletion.AdicCauchySequence I R) :
    AdicCompletion.AdicCauchySequence I R :=
  ⟨fun n => D (a (n + 1)), by
    intro m n hmn
    apply SModEq.sub_mem.mpr
    have h : a (m + 1) - a (n + 1) ∈ I ^ (m + 1) := by
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
        (SModEq.sub_mem.mp (a.property (Nat.add_le_add_right hmn 1)))
    have hD := D.map_mem_pow_succ I m h
    rw [map_sub] at hD
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hD⟩

private theorem adicSequence_congr
    (a b : AdicCompletion.AdicCauchySequence I R)
    (h : AdicCompletion.mk I R a = AdicCompletion.mk I R b) :
    AdicCompletion.mk I R (D.adicSequence I a) =
      AdicCompletion.mk I R (D.adicSequence I b) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  apply D.quotient_derivative_eq I n
  have hn := congrArg (AdicCompletion.evalₐ I (n + 1)) h
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk] at hn
  exact hn

/-- The function on the adic completion induced by differentiating Cauchy representatives. -/
def adicFunction (x : AdicCompletion I R) : AdicCompletion I R :=
  AdicCompletion.mk I R
    (D.adicSequence I ((AdicCompletion.mk_surjective I R x).choose))

private theorem adicFunction_mk (a : AdicCompletion.AdicCauchySequence I R) :
    D.adicFunction I (AdicCompletion.mk I R a) =
      AdicCompletion.mk I R (D.adicSequence I a) :=
  D.adicSequence_congr I _ a
    (AdicCompletion.mk_surjective I R (AdicCompletion.mk I R a)).choose_spec

private theorem eval_adicFunction_of_rep (n : ℕ)
    (x : AdicCompletion I R) (r : R)
    (hr : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk (I ^ (n + 1)) r) :
    AdicCompletion.evalₐ I n (D.adicFunction I x) = Ideal.Quotient.mk (I ^ n) (D r) := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [D.adicFunction_mk, AdicCompletion.evalₐ_mk]
  apply D.quotient_derivative_eq I n
  rw [AdicCompletion.evalₐ_mk] at hr
  exact hr

private theorem eval_of_succ_rep (n : ℕ) (x : AdicCompletion I R) (r : R)
    (hr : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk (I ^ (n + 1)) r) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := by
  calc
    AdicCompletion.evalₐ I n x =
        Ideal.Quotient.factorPow I (Nat.le_succ n)
          (AdicCompletion.evalₐ I (n + 1) x) :=
      (AdicCompletion.factorPow_evalRing I (Nat.le_succ n) x).symm
    _ = Ideal.Quotient.factorPow I (Nat.le_succ n)
        (Ideal.Quotient.mk (I ^ (n + 1)) r) :=
      congrArg (Ideal.Quotient.factorPow I (Nat.le_succ n)) hr
    _ = Ideal.Quotient.mk (I ^ n) r := rfl

/-- The additive extension of the derivation to the adic completion. -/
def adicAddHom : AdicCompletion I R →+ AdicCompletion I R where
  toFun := D.adicFunction I
  map_zero' := by
    apply AdicCompletion.ext_evalₐ
    intro n
    simpa only [map_zero] using
      D.eval_adicFunction_of_rep I n 0 0 (by rw [map_zero, map_zero])
  map_add' x y := by
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    have hsum : AdicCompletion.evalₐ I (n + 1) (x + y) =
        Ideal.Quotient.mk (I ^ (n + 1)) (r + s) := by
      rw [map_add, ← hr, ← hs, map_add]
    rw [D.eval_adicFunction_of_rep I n (x + y) (r + s) hsum,
      map_add (AdicCompletion.evalₐ I n),
      D.eval_adicFunction_of_rep I n x r hr.symm,
      D.eval_adicFunction_of_rep I n y s hs.symm, map_add D, map_add]

private theorem adicFunction_leibniz (x y : AdicCompletion I R) :
    D.adicFunction I (x * y) =
      x * D.adicFunction I y + y * D.adicFunction I x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have hprod : AdicCompletion.evalₐ I (n + 1) (x * y) =
      Ideal.Quotient.mk (I ^ (n + 1)) (r * s) := by
    rw [map_mul, ← hr, ← hs, map_mul]
  rw [D.eval_adicFunction_of_rep I n (x * y) (r * s) hprod,
    map_add (AdicCompletion.evalₐ I n), map_mul (AdicCompletion.evalₐ I n),
    map_mul (AdicCompletion.evalₐ I n), eval_of_succ_rep I n x r hr.symm,
    eval_of_succ_rep I n y s hs.symm,
    D.eval_adicFunction_of_rep I n x r hr.symm,
    D.eval_adicFunction_of_rep I n y s hs.symm,
    D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]

/-- The actual extension of a derivation to the native adic completion. -/
def adicCompletion : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Derivation.mk' (D.adicAddHom I).toIntLinearMap (fun x y => by
    exact D.adicFunction_leibniz I x y)

/-- Evaluation of the extended derivation is determined by a representative
one ideal-power level higher. -/
theorem eval_adicCompletion_of_rep (n : ℕ)
    (x : AdicCompletion I R) (r : R)
    (hr : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk (I ^ (n + 1)) r) :
    AdicCompletion.evalₐ I n (D.adicCompletion I x) = Ideal.Quotient.mk (I ^ n) (D r) :=
  D.eval_adicFunction_of_rep I n x r hr

/-- The extension agrees with the original derivation on every original
ring element, through the canonical completion map. -/
theorem adicCompletion_algebraMap (r : R) :
    D.adicCompletion I (algebraMap R (AdicCompletion I R) r) =
      algebraMap R (AdicCompletion I R) (D r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  exact (D.eval_adicCompletion_of_rep I n _ r
    (AdicCompletion.evalₐ_of I (n + 1) r)).trans
      (AdicCompletion.evalₐ_of I n (D r)).symm

end Derivation
