/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith

/-! # All-orders growth after a tame parameter substitution

The coefficient of degree `n` in `B^m` has order at least `e*n+m`.
After multiplication by a coefficient of order at least `-c*m`, only
`m ≤ n` contributes. For `1 ≤ c ≤ e` this gives the uniform lower bound
`(e-c+1)*n` for the actual composition. Vanishing coefficients are kept
separate because the place convention is `ord 0 = 0`.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_finset_sum_lower_of_ne_zero (v : Place K F)
    {ι : Type*} (s : Finset ι) (f : ι → F) (d : ℤ)
    (h : ∀ i ∈ s, f i ≠ 0 → d ≤ v.ord (f i))
    (hs : (∑ i ∈ s, f i) ≠ 0) : d ≤ v.ord (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (hs (by rw [Finset.sum_empty]))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi] at hs ⊢
    have hrest : ∀ j ∈ s, f j ≠ 0 → d ≤ v.ord (f j) :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    by_cases hi0 : f i = 0
    · rw [hi0, zero_add] at hs ⊢
      exact ih hrest hs
    by_cases hs0 : (∑ j ∈ s, f j) = 0
    · rw [hs0, add_zero]
      exact h i (Finset.mem_insert_self i s) hi0
    exact (le_min (h i (Finset.mem_insert_self i s) hi0) (ih hrest hs0)).trans
      (v.min_ord_le_ord_add hi0 hs0 hs)

/-- Actual convolution coefficients retain an arbitrary integer offset for
every positive-degree factor, allowing both zeros and poles in a parameter. -/
theorem powerSeries_pow_coeff_ord_affine (v : Place K F)
    (B : PowerSeries F) (e b : ℤ) (hB0 : PowerSeries.constantCoeff B = 0)
    (hB : ∀ n, 0 < n → PowerSeries.coeff n B ≠ 0 →
      e * n + b ≤ v.ord (PowerSeries.coeff n B))
    (m n : ℕ) (hne : PowerSeries.coeff n (B ^ m) ≠ 0) :
    e * n + b * m ≤ v.ord (PowerSeries.coeff n (B ^ m)) := by
  induction m generalizing n with
  | zero =>
    by_cases hn : n = 0
    · subst n
      simp only [pow_zero, PowerSeries.coeff_zero_eq_constantCoeff, map_one,
        v.ord_one, Nat.cast_zero, mul_zero, add_zero, le_refl]
    · exact False.elim (hne (by
        simp only [pow_zero, PowerSeries.coeff_one, ite_eq_right hn]))
  | succ m ih =>
    rw [pow_succ, PowerSeries.coeff_mul] at hne ⊢
    apply ord_finset_sum_lower_of_ne_zero v _ _ _ ?_ hne
    intro ij hij hprod
    have hijsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    have hleft := left_ne_zero_of_mul hprod
    have hright := right_ne_zero_of_mul hprod
    have hj : 0 < ij.2 := by
      by_contra hpos
      have hz : ij.2 = 0 := by omega
      exact hright (by rw [hz, PowerSeries.coeff_zero_eq_constantCoeff, hB0])
    rw [v.ord_mul hleft hright]
    have hn : (n : ℤ) = (ij.1 : ℤ) + (ij.2 : ℤ) := by
      exact_mod_cast hijsum.symm
    have hleftBound := ih ij.1 hleft
    have hrightBound := hB ij.2 hj hright
    push_cast
    rw [hn]
    nlinarith

/-- The tame displacement has one extra unit of order in each factor. -/
theorem powerSeries_pow_coeff_ord_linear (v : Place K F)
    (B : PowerSeries F) (e : ℕ) (hB0 : PowerSeries.constantCoeff B = 0)
    (hB : ∀ n, 0 < n → PowerSeries.coeff n B ≠ 0 →
      ((e * n + 1 : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n B))
    (m n : ℕ) (hne : PowerSeries.coeff n (B ^ m) ≠ 0) :
    ((e * n + m : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (B ^ m)) := by
  have h := v.powerSeries_pow_coeff_ord_affine B e 1 hB0
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hB) m n hne
  simpa only [one_mul, Nat.cast_add, Nat.cast_mul] using h

private theorem coeff_subst_truncated (A B : PowerSeries F)
    (hB0 : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst B A) =
      ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff m A * PowerSeries.coeff n (B ^ m) := by
  classical
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hB0)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro m hm
  change PowerSeries.coeff m A * PowerSeries.coeff n (B ^ m) ≠ 0 at hm
  apply Finset.mem_range.mpr
  by_contra hmn
  have hnm : n < m := by omega
  have hzero : PowerSeries.coeff n (B ^ m) = 0 :=
    PowerSeries.coeff_of_lt_order n ((show (n : ℕ∞) < (m : ℕ∞) by
      exact_mod_cast hnm).trans_le
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero m hB0))
  exact hm (by rw [hzero, mul_zero])

/-- Substitution into the tame displacement constructs a zero-constant
series whose every nonzero coefficient has the prescribed positive linear
order. The estimate includes degree zero, where its nonzero premise is false. -/
theorem powerSeries_subst_tame_order (v : Place K F)
    (A B : PowerSeries F) (c e : ℕ) (hc : 1 ≤ c) (hce : c ≤ e)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hA : ∀ m, PowerSeries.coeff m A ≠ 0 →
      -((c * m : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff m A))
    (hB : ∀ n, 0 < n → PowerSeries.coeff n B ≠ 0 →
      ((e * n + 1 : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n B)) :
    PowerSeries.constantCoeff (PowerSeries.subst B A) = 0 ∧
      ∀ n, PowerSeries.coeff n (PowerSeries.subst B A) ≠ 0 →
        (((e - c + 1) * n : ℕ) : ℤ) ≤
          v.ord (PowerSeries.coeff n (PowerSeries.subst B A)) := by
  classical
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero hB0 A hA0, ?_⟩
  intro n hne
  have hcoeff := coeff_subst_truncated A B hB0 n
  rw [hcoeff] at hne ⊢
  apply ord_finset_sum_lower_of_ne_zero v _ _ _ ?_ hne
  intro m hm hprod
  have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
  have hleft := left_ne_zero_of_mul hprod
  have hright := right_ne_zero_of_mul hprod
  have ha := hA m hleft
  have hb := v.powerSeries_pow_coeff_ord_linear B e hB0 hB m n hright
  rw [v.ord_mul hleft hright]
  have hnumeric : (((e - c + 1) * n : ℕ) : ℤ) ≤
      -((c * m : ℕ) : ℤ) + ((e * n + m : ℕ) : ℤ) := by
    have hcInt : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
    have hmnInt : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hmul := mul_nonneg (sub_nonneg.mpr hcInt) (sub_nonneg.mpr hmnInt)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hce, Nat.cast_one]
    nlinarith
  exact hnumeric.trans (add_le_add ha hb)

/-- Substitution transports an affine coefficient-order bound through a
parameter with a possibly negative offset. This accommodates a fixed global
parameter which has poles at the boundary. -/
theorem powerSeries_subst_coeff_ord_affine (v : Place K F)
    (A B : PowerSeries F) (a c e b : ℤ) (hbc : b ≤ c)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hA : ∀ m, PowerSeries.coeff m A ≠ 0 →
      a - c * m ≤ v.ord (PowerSeries.coeff m A))
    (hB : ∀ n, 0 < n → PowerSeries.coeff n B ≠ 0 →
      e * n + b ≤ v.ord (PowerSeries.coeff n B))
    (n : ℕ) (hne : PowerSeries.coeff n (PowerSeries.subst B A) ≠ 0) :
    a + (e + b - c) * n ≤ v.ord (PowerSeries.coeff n (PowerSeries.subst B A)) := by
  classical
  rw [coeff_subst_truncated A B hB0 n] at hne ⊢
  apply ord_finset_sum_lower_of_ne_zero v _ _ _ ?_ hne
  intro m hm hprod
  have hmn : (m : ℤ) ≤ (n : ℤ) := by
    have hnat : m ≤ n := by have := Finset.mem_range.mp hm; omega
    exact_mod_cast hnat
  have hleft := left_ne_zero_of_mul hprod
  have hright := right_ne_zero_of_mul hprod
  have ha := hA m hleft
  have hb := v.powerSeries_pow_coeff_ord_affine B e b hB0 hB m n hright
  rw [v.ord_mul hleft hright]
  have hmul := mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hmn)
  nlinarith

end AlgebraicCurve.Place
