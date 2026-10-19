/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions

/-!
# Place exists ord eq one of ord sum eq one
-/

namespace AlgebraicCurve.Place

theorem exists_ord_eq_one_of_ord_sum_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i = 0 ∨ 1 ≤ v.ord (f i))
    (h : v.ord (∑ i ∈ s, algebraMap K F (c i) * f i) = 1) :
    ∃ i ∈ s, v.ord (f i) = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hterm : ∀ i ∈ s,
      v.adicValuation (algebraMap K F (c i) * f i) ≤ WithZero.exp (-(2 : ℤ)) := by
    intro i hi
    rcases hf i hi with h0 | h1
    · rw [h0, mul_zero, map_zero]
      exact zero_le
    · have h2 : (2 : ℤ) ≤ v.ord (f i) := by
        have := hcon i hi
        omega
      rw [map_mul]
      calc v.adicValuation (algebraMap K F (c i)) * v.adicValuation (f i)
          ≤ 1 * WithZero.exp (-(2 : ℤ)) :=
            mul_le_mul' (v.adicValuation_algebraMap_le_one (c i))
              ((v.adicValuation_le_exp_iff (f := f i) (n := -(2 : ℤ))).mpr (Or.inr h2))
        _ = WithZero.exp (-(2 : ℤ)) := one_mul _
  have hsum := (v.adicValuation_le_exp_iff (n := -(2 : ℤ))).mp (v.adicValuation.map_sum_le hterm)
  rcases hsum with h0 | h2
  · rw [h0, AlgebraicCurve.Place.ord_zero] at h
    exact zero_ne_one h
  · omega

end AlgebraicCurve.Place
