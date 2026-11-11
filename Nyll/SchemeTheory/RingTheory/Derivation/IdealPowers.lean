/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Derivations and ideal powers

The Leibniz rule implies that a derivation decreases the order of every
ideal power by at most one. This supplies both adic continuity and the
cotangent obstruction used in regular quotient criteria.
-/

@[expose] public section

namespace Derivation

universe u v

variable {K : Type u} [CommRing K] {R : Type v} [CommRing R] [Algebra K R]
    (D : Derivation K R R) (I : Ideal R)

/-- A derivation decreases ideal-adic order by at most one. -/
theorem map_mem_pow_succ (n : ℕ) {x : R} (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact (Submodule.mem_top : D x ∈ (⊤ : Submodule R R))
  | succ n ih =>
      rw [pow_succ'] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        apply Ideal.add_mem
        · rw [pow_succ']
          exact Ideal.mul_mem_mul ha (ih hb)
        · exact Ideal.mul_mem_right _ _ hb
      · intro a b ha hb
        rw [map_add]
        exact Ideal.add_mem _ ha hb

end Derivation
