/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Completeness of modules annihilated by an ideal power

An adic Cauchy sequence in a module killed by a fixed ideal power is
eventually constant. Its value at that exponent supplies the limit, and
the same annihilation proves separatedness. Neither finiteness nor
completeness of the coefficient ring is needed.

This applies to the actual finite stages of a formal module system over
an affine coordinate ring, even when that coordinate ring is not complete.
-/

namespace IsAdicComplete

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)
  (M : Type v) [AddCommGroup M] [Module R M]

/-- A module annihilated by one ideal power is complete for that ideal. -/
theorem of_pow_smul_top_eq_bot (n : ℕ)
    (hpow : I ^ n • (⊤ : Submodule R M) = ⊥) : IsAdicComplete I M where
  haus' x hx := by
    have h := SModEq.sub_mem.mp (hx n)
    rw [hpow, Submodule.mem_bot, sub_zero] at h
    exact h
  prec' f hf := by
    refine ⟨f n, fun k => ?_⟩
    by_cases hk : k ≤ n
    · exact hf hk
    · have h := SModEq.sub_mem.mp (hf (Nat.le_of_lt (Nat.lt_of_not_ge hk)))
      rw [hpow, Submodule.mem_bot] at h
      have heq : f n = f k := sub_eq_zero.mp h
      rw [heq]

end IsAdicComplete
