/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusLocalUnits
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.GroupTheory.OrderOfElement

/-!
# Positive-characteristic units retain the full modulus

In characteristic `p`, the image of `1 + π` in the units modulo `m^(p+1)`
has order `p²`. This rules out replacing the whole principal-unit group by
an additive group killed by `p`. It is an assertion about actual truncated
local rings, without any assumption of scheme representability.
-/

noncomputable section

namespace AlgebraicCurve.Place

open LubinTate.Valuations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The thickness `p + 1` already detects elements of order `p²` in
characteristic `p`; the witness lifts from the principal unit `1 + π`. -/
theorem exists_truncatedUnit_order_eq_prime_sq (v : Place K F)
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ u : v.toValuationSubringˣ,
      u ∈ v.congruenceUnitSubgroup 1 ∧
      orderOf (unitReduction
        ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ (p + 1)) u) = p ^ 2 := by
  have : CharP v.toValuationSubring p :=
    v.toValuationSubring.subtype.charP Subtype.val_injective p
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  let u : v.toValuationSubringˣ := higherUnitOneAdd hπ 1 (le_refl 1) 1
  have hu : (u : v.toValuationSubring) = 1 + π := by
    change ((higherUnitOneAdd hπ 1 (le_refl 1) 1 : v.toValuationSubringˣ) :
      v.toValuationSubring) = _
    rw [higherUnitOneAdd_val, pow_one, mul_one]
  refine ⟨u, ?_, ?_⟩
  · rw [v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ]
    exact (higherUnitOneAdd hπ 1 (le_refl 1) 1).property
  let I : Ideal v.toValuationSubring :=
    (IsLocalRing.maximalIdeal v.toValuationSubring) ^ (p + 1)
  let q := unitReduction I u
  have hpow (n : ℕ) :
      ((q ^ (p ^ n) : (v.toValuationSubring ⧸ I)ˣ) : v.toValuationSubring ⧸ I) =
        Ideal.Quotient.mk I (1 + π ^ (p ^ n)) := by
    change (Ideal.Quotient.mk I (u : v.toValuationSubring)) ^ (p ^ n) = _
    rw [← map_pow, hu, add_pow_char_pow, one_pow]
  have hne : q ^ p ≠ 1 := by
    intro h
    have he := congrArg (fun a : (v.toValuationSubring ⧸ I)ˣ =>
      (a : v.toValuationSubring ⧸ I)) h
    have he' : Ideal.Quotient.mk I (1 + π ^ p) = Ideal.Quotient.mk I 1 := by
      have heq : ((q ^ p : (v.toValuationSubring ⧸ I)ˣ) : v.toValuationSubring ⧸ I) =
          Ideal.Quotient.mk I (1 + π ^ p) := by
        simpa only [pow_one] using hpow 1
      rw [heq] at he
      exact he
    have hm : π ^ p ∈ I := by
      have hm' := Ideal.Quotient.eq.mp he'
      simpa only [add_sub_cancel_left] using hm'
    change π ^ p ∈ (IsLocalRing.maximalIdeal v.toValuationSubring) ^ (p + 1) at hm
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
    have hle := (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).mp hm
    omega
  have hfin : q ^ (p ^ 2) = 1 := by
    apply Units.ext
    rw [hpow 2]
    change Ideal.Quotient.mk I (1 + π ^ (p ^ 2)) = Ideal.Quotient.mk I 1
    apply Ideal.Quotient.eq.mpr
    rw [add_sub_cancel_left]
    change π ^ (p ^ 2) ∈ (IsLocalRing.maximalIdeal v.toValuationSubring) ^ (p + 1)
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    apply pow_dvd_pow
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    nlinarith
  have he : orderOf q = p ^ (1 + 1) :=
    orderOf_eq_prime_pow (n := 1) (by simpa only [pow_one] using hne) hfin
  exact he

end AlgebraicCurve.Place
