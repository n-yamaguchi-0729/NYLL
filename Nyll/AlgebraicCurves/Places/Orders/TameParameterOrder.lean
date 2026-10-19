/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.TameInverseRoot
import Nyll.AlgebraicCurves.Places.Basic

/-! # Exact coefficient orders of the tame parameter displacement

Hensel's constructed root gives the branch change for `s = π^e` under
`s ↦ s/(1+sT)`. Every nonzero coefficient of its displacement in degree `n>0`
has order exactly `e*n+1`. Zero coefficients are handled separately, respecting
the library convention `ord 0 = 0`.
-/

noncomputable section

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual tame root change has uniform positive coefficient orders,
in all degrees and in every characteristic where the exponent is invertible. -/
theorem exists_tameParameterChange_exact_orders (v : Place K F)
    (e : ℕ) (he : (e : K) ≠ 0) (π : F) (hπ : v.ord π = 1) :
    ∃ B : PowerSeries K,
      PowerSeries.constantCoeff B = 1 ∧ B ^ e * (1 + PowerSeries.X) = 1 ∧
      let S := PowerSeries.C π * PowerSeries.rescale (π ^ e)
        (PowerSeries.map (algebraMap K F) B)
      PowerSeries.constantCoeff S = π ∧
      S ^ e * (1 + PowerSeries.C (π ^ e) * PowerSeries.X) = PowerSeries.C (π ^ e) ∧
      ∀ n : ℕ, 0 < n → PowerSeries.coeff n (S - PowerSeries.C π) ≠ 0 →
        v.ord (PowerSeries.coeff n (S - PowerSeries.C π)) = ((e * n + 1 : ℕ) : ℤ) := by
  obtain ⟨B, hB0, hBe, hS⟩ := PowerSeries.exists_tameParameterChange e he π
  refine ⟨B, hB0, hBe, ?_⟩
  intro S
  refine ⟨hS.1, hS.2, ?_⟩
  intro n hn hc
  have heq : PowerSeries.coeff n (S - PowerSeries.C π) =
      π ^ (e * n + 1) * algebraMap K F (PowerSeries.coeff n B) := by
    change PowerSeries.coeff n (PowerSeries.C π * _ - PowerSeries.C π) = _
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_of_ne_zero (Nat.ne_of_gt hn),
      sub_zero, PowerSeries.coeff_rescale, PowerSeries.coeff_map, ← pow_mul, pow_succ]
    ring
  have hπ0 : π ≠ 0 := by
    intro hzero
    rw [hzero, v.ord_zero] at hπ
    exact zero_ne_one hπ
  rw [heq] at hc ⊢
  rw [v.ord_mul (pow_ne_zero _ hπ0) (right_ne_zero_of_mul hc), v.ord_algebraMap, add_zero]
  have h := v.ord_zpow π ((e * n + 1 : ℕ) : ℤ)
  simpa only [zpow_natCast, hπ, mul_one] using h

end AlgebraicCurve.Place
