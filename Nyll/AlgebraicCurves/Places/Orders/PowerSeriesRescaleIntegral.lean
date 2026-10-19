/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith

/-! # Integral rescaling of a series with a linear pole bound

For a series with zero constant coefficient, a parameter of order at least
`2b` clears every coefficient pole bounded by `b(n+1)`. The resulting series
over the actual valuation ring is constructed coefficient by coefficient.
-/

noncomputable section

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Rescaling by an element of order at least `2b` makes every coefficient
integral when the constant coefficient vanishes and the poles grow at most linearly. -/
theorem powerSeries_rescale_coeff_mem (v : Place K F)
    (A : PowerSeries F) (b : ℕ) (r : F)
    (hzero : PowerSeries.constantCoeff A = 0)
    (hbound : ∀ n, -((b * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A))
    (hr : ((2 * b : ℕ) : ℤ) ≤ v.ord r) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.rescale r A) ∈ v.toValuationSubring := by
  rw [PowerSeries.coeff_rescale]
  by_cases hn : n = 0
  · subst n
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero, mul_zero]
    exact zero_mem _
  by_cases hprod : r ^ n * PowerSeries.coeff n A = 0
  · rw [hprod]
    exact zero_mem _
  apply v.mem_toValuationSubring_of_ord_nonneg
  rw [v.ord_mul (left_ne_zero_of_mul hprod) (right_ne_zero_of_mul hprod)]
  have hpow : v.ord (r ^ n) = (n : ℤ) * v.ord r := by
    simpa only [zpow_natCast] using v.ord_zpow r (n : ℤ)
  rw [hpow]
  have hmul := mul_le_mul_of_nonneg_left hr (Int.natCast_nonneg n)
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnonneg := mul_nonneg (Int.natCast_nonneg b) (sub_nonneg.mpr hn')
  have hcoeff := hbound n
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hcoeff hmul
  nlinarith

/-- The integral rescaling is an actual series over the valuation ring,
whose coefficientwise inclusion recovers the original rescaled series. -/
theorem exists_rescale_powerSeries_valuationSubring (v : Place K F)
    (A : PowerSeries F) (b : ℕ) (r : F)
    (hzero : PowerSeries.constantCoeff A = 0)
    (hbound : ∀ n, -((b * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A))
    (hr : ((2 * b : ℕ) : ℤ) ≤ v.ord r) :
    ∃ B : PowerSeries v.toValuationSubring,
      B.map v.toValuationSubring.subtype = PowerSeries.rescale r A := by
  let B : PowerSeries v.toValuationSubring := PowerSeries.mk fun n =>
    ⟨PowerSeries.coeff n (PowerSeries.rescale r A),
      v.powerSeries_rescale_coeff_mem A b r hzero hbound hr n⟩
  refine ⟨B, ?_⟩
  apply PowerSeries.ext
  intro n
  simp only [B, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rfl

/-- The explicit power `π^(2b)` of any order-one parameter clears all the
linear coefficient poles of a series with zero constant coefficient. -/
theorem exists_uniformizer_rescale_powerSeries_valuationSubring (v : Place K F)
    (A : PowerSeries F) (b : ℕ) (π : F) (hπ : v.ord π = 1)
    (hzero : PowerSeries.constantCoeff A = 0)
    (hbound : ∀ n, -((b * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A)) :
    ∃ B : PowerSeries v.toValuationSubring,
      B.map v.toValuationSubring.subtype = PowerSeries.rescale (π ^ (2 * b)) A := by
  apply v.exists_rescale_powerSeries_valuationSubring A b (π ^ (2 * b)) hzero hbound
  have h := v.ord_zpow π ((2 * b : ℕ) : ℤ)
  rw [zpow_natCast, hπ, mul_one] at h
  exact h.ge

end AlgebraicCurve.Place
