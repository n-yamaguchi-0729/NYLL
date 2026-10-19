/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Abel

/-!
# Adic exactness from an explicit filtration estimate

The finite-module exactness theorem for completion uses Artin–Rees only
to compare the filtration induced on a submodule with its own adic
filtration. The same estimate can hold for an infinite module, for
example for a direct sum of copies of one inclusion of finite modules.

Here the estimate is stated directly and used to construct the required
Cauchy preimages. In the direct-sum application the estimate is proved
coordinate by coordinate from a single Artin–Rees bound. Neither
exactness after completion nor the existence of a completed lift is an
input to this construction.
-/

noncomputable section

namespace AdicCompletion

universe u v w t

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type t} [AddCommGroup P] [Module R P]

/-- An explicit uniform comparison of filtrations makes the map on
completions injective; the modules need not be finite. -/
theorem map_injective_of_adic_bound (f : M →ₗ[R] N) (k : ℕ)
    (hbound : ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • ⊤ : Submodule R N) ≤
        (I ^ n • ⊤ : Submodule R M)) :
    Function.Injective (map I f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x
  intro a ha
  apply AdicCompletion.ext
  intro n
  have hfa : f (a (n + k)) ∈ (I ^ (n + k) • ⊤ : Submodule R N) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg (fun z : AdicCompletion I N => z.val (n + k)) ha
  have hmem : a (n + k) ∈ (I ^ n • ⊤ : Submodule R M) := hbound n hfa
  change Submodule.Quotient.mk (a n) = 0
  rw [← AdicCauchySequence.mk_eq_mk (Nat.le_add_right n k) a]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hmem

/-- Exactness of completion under an explicit uniform filtration bound.

Approximate preimages at precision `n + k` automatically form an adic
Cauchy sequence at precision `n`. This applies to infinite modules once
the displayed estimate has been established. -/
theorem map_exact_of_adic_bound (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (k : ℕ)
    (hbound : ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • ⊤ : Submodule R N) ≤
        (I ^ n • ⊤ : Submodule R M)) :
    Function.Exact (map I f) (map I g) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · rw [map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · intro z
    apply AdicCompletion.induction_on I N z
    intro b hb
    have happrox (n : ℕ) : ∃ y : M,
        f y - b (n + k) ∈ (I ^ (n + k) • ⊤ : Submodule R N) := by
      have hgb : g (b (n + k)) ∈ (I ^ (n + k) • ⊤ : Submodule R P) := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrArg (fun z : AdicCompletion I P => z.val (n + k)) hb
      have hgmem : g (b (n + k)) ∈
          Submodule.map g (I ^ (n + k) • ⊤ : Submodule R N) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
        exact hgb
      obtain ⟨d, hd, hgd⟩ := hgmem
      obtain ⟨y, hy⟩ := (hfg (b (n + k) - d)).mp (by
        rw [map_sub, hgd, sub_self])
      refine ⟨y, ?_⟩
      rw [hy, sub_sub_cancel_left]
      exact Submodule.neg_mem _ hd
    choose a ha using happrox
    have hcauchy (n : ℕ) :
        a n ≡ a (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] := by
      apply SModEq.sub_mem.mpr
      apply hbound n
      change f (a n - a (n + 1)) ∈ (I ^ (n + k) • ⊤ : Submodule R N)
      have hnext : f (a (n + 1)) - b (n + 1 + k) ∈
          (I ^ (n + k) • ⊤ : Submodule R N) :=
        Submodule.smul_mono_left
          (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) k)) (ha (n + 1))
      have hdiff : b (n + k) - b (n + 1 + k) ∈
          (I ^ (n + k) • ⊤ : Submodule R N) :=
        SModEq.sub_mem.mp (b.property (Nat.add_le_add_right (Nat.le_succ n) k))
      have heq : f (a n - a (n + 1)) =
          (f (a n) - b (n + k)) + (b (n + k) - b (n + 1 + k)) -
            (f (a (n + 1)) - b (n + 1 + k)) := by
        rw [map_sub]
        abel
      rw [heq]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (ha n) hdiff) hnext
    let c : AdicCauchySequence I M := AdicCauchySequence.mk I M a hcauchy
    refine ⟨AdicCompletion.mk I M c, ?_⟩
    apply AdicCompletion.ext
    intro n
    change Submodule.Quotient.mk (f (a n)) =
      Submodule.Quotient.mk (b n)
    rw [← AdicCauchySequence.mk_eq_mk (Nat.le_add_right n k) b]
    apply (Submodule.Quotient.eq _).mpr
    exact Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.le_add_right n k)) (ha n)

end AdicCompletion
