/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Batteries.Tactic.Init
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Set
import Nyll.SchemeTheory.RingTheory.Polynomial.Macaulay

/-!
# Nat exists polynomial forall eval eq of forall eq macaulay Pow
-/

section ProofImplementation

open _root_.Nat.Macaulay

namespace AlgebraicCurves.Foundations.Polynomial.Proofs
namespace Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow

namespace PolyMaxSol

/-- The sequence obtained by iterating Macaulay powers with successively increasing degrees. -/
def G (d a : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => Nat.macaulayPow (d + j + 1) (G d a j)

theorem G_zero (d a : ℕ) : G d a 0 = a := rfl
theorem G_succ (d a j : ℕ) : G d a (j + 1) = Nat.macaulayPow (d + j + 1) (G d a j) := rfl

theorem G_zero_mid : ∀ (d j : ℕ), G d 0 j = 0
  | d, 0 => rfl
  | d, j + 1 => by rw [G_succ, G_zero_mid d j, macaulayPow_zero_right]

theorem top_G (d a : ℕ) : ∀ j : ℕ, top (d + j) (G d a j) = top d a + j
  | 0 => rfl
  | j + 1 => by
      rw [G_succ, show d + (j + 1) = (d + j) + 1 from rfl, top_macaulayPow, top_G d a j]; omega

/-- The auxiliary Macaulay-growth sequence, with the degree-zero case set to zero. -/
def tail : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | d + 1, r, j => G d r j

theorem rem_G : ∀ (d a j : ℕ), rem (d + j) (G d a j) = tail d (rem d a) j
  | 0, a, 0 => by simp only [Nat.add_zero, tail, G_zero, rem_zero_left]
  | 0, a, j + 1 => by
      rw [G_succ, show 0 + (j + 1) = (0 + j) + 1 from rfl, rem_macaulayPow, rem_G 0 a j]
      simp only [tail, macaulayPow_zero_right]
  | d + 1, a, 0 => by simp only [Nat.add_zero, tail, G_zero]
  | d + 1, a, j + 1 => by
      rw [G_succ, show d + 1 + (j + 1) = (d + 1 + j) + 1 from rfl, rem_macaulayPow, rem_G (d + 1) a
        j]
      simp only [tail]
      rw [G_succ, show d + 1 + j = d + j + 1 by omega]

theorem G_eq (d a j : ℕ) : G d a j = (top d a + j).choose (d + j + 1) + tail d (rem d a) j := by
  have h := rem_add_choose (d + j) (G d a j)
  rw [top_G, rem_G] at h
  omega

theorem exists_poly_choose (t d : ℕ) (ht : d ≤ t) :
    ∃ P : Polynomial ℚ, ∀ j : ℕ, (((t + j).choose (d + j + 1) : ℕ) : ℚ) = P.eval (j : ℚ) := by
  rcases Nat.eq_or_lt_of_le ht with rfl | hlt
  · refine ⟨0, fun j => ?_⟩
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, Polynomial.eval_zero]
  · set c := t - (d + 1) with hc
    refine ⟨Polynomial.C ((c.factorial : ℚ)⁻¹) * (descPochhammer ℚ c).comp (Polynomial.X +
      Polynomial.C (t : ℚ)),
      fun j => ?_⟩
    have hsymm : (t + j).choose (d + j + 1) = (t + j).choose c := by
      rw [show c = (t + j) - (d + j + 1) by omega]
      exact (Nat.choose_symm (by omega)).symm
    rw [hsymm, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X,
      Polynomial.eval_C, show ((j : ℚ) + (t : ℚ)) = ((t + j : ℕ) : ℚ) by push_cast; ring,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    have hf : (c.factorial : ℚ) ≠ 0 := by exact_mod_cast c.factorial_ne_zero
    push_cast
    field_simp

theorem exists_poly_tail_zero (r : ℕ) : ∃ P : Polynomial ℚ, ∀ j : ℕ, ((tail 0 r j : ℕ) : ℚ) =
  P.eval (j : ℚ) :=
  ⟨0, fun j => by simp only [tail, Nat.cast_zero, Polynomial.eval_zero]⟩

theorem exists_poly_G : ∀ (d a : ℕ), ∃ P : Polynomial ℚ, ∀ j : ℕ, ((G d a j : ℕ) : ℚ) = P.eval (j :
  ℚ)
  | 0, a => by
      obtain ⟨P, hP⟩ := exists_poly_choose (top 0 a) 0 (d_le_top 0 a)
      refine ⟨P, fun j => ?_⟩
      rw [G_eq]; simp only [tail, add_zero]; rw [← hP]
  | d + 1, a => by
      obtain ⟨P, hP⟩ := exists_poly_choose (top (d + 1) a) (d + 1) (d_le_top (d + 1) a)
      obtain ⟨Q, hQ⟩ := exists_poly_G d (rem (d + 1) a)
      refine ⟨P + Q, fun j => ?_⟩
      rw [G_eq, Polynomial.eval_add, ← hP, ← hQ]
      simp only [tail]; push_cast; rfl

end PolyMaxSol

open PolyMaxSol in
theorem _root_.Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
    (H : ℕ → ℕ) (D₀ : ℕ) (hD₀ : 1 ≤ D₀)
    (hH : ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e)) :
    ∃ P : Polynomial ℚ, ∀ e, D₀ ≤ e → (H e : ℚ) = P.eval (e : ℚ) := by
  obtain ⟨d, rfl⟩ : ∃ d, D₀ = d + 1 := ⟨D₀ - 1, by omega⟩
  have hG : ∀ j : ℕ, H (d + 1 + j) = PolyMaxSol.G d (H (d + 1)) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [PolyMaxSol.G_succ, ← ih, show d + j + 1 = d + 1 + j
          by omega, show d + 1 + (j + 1) = (d + 1 + j) + 1 by omega]
        exact hH _ (by omega)
  obtain ⟨P, hP⟩ := PolyMaxSol.exists_poly_G d (H (d + 1))
  refine ⟨P.comp (Polynomial.X - Polynomial.C ((d + 1 : ℕ) : ℚ)), fun e he => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, e = d + 1 + j := ⟨e - (d + 1), by omega⟩
  rw [hG, hP, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  congr 1
  push_cast; ring
end Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
end AlgebraicCurves.Foundations.Polynomial.Proofs
end ProofImplementation
