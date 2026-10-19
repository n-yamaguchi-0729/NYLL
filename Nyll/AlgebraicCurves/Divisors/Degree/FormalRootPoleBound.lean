/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Orders.RationalSeriesPoleBound
import Nyll.AlgebraicCurves.Divisors.Degree.FiniteTypePoleBound

/-! # Weighted coefficient bounds for algebraic formal equations

For a simple root with displacement `Z = X * W`, removing the linear term
gives monomials `c * X^s * W^j` satisfying `j ≤ 2 * s`. This condition ensures
that every nonconstant occurrence of `W` uses only earlier coefficients.
The estimate below is derived from the finite coefficients, with no assumed
growth bound for `W`.

The conversion of an arbitrary simple-root polynomial to this weighted
equation remains a separate algebraic step. The existence of the actual
formal root is supplied by `FormalSimpleRoot`, not assumed by an existence
theorem in this file.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_coeff_pow_ge_weight
    (W : PowerSeries F) (M j n : ℕ)
    (hW : ∀ r ≤ n, -((M * (2 * r + 1) : ℕ) : ℤ) ≤
      v.ord (PowerSeries.coeff r W)) :
    -((M * (2 * n + j) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (W ^ j)) := by
  induction j generalizing n with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    by_cases hn : n = 0
    · rw [ite_eq_left hn, v.ord_one]
      omega
    · rw [ite_eq_right hn, v.ord_zero]
      omega
  | succ j ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    apply ord_finset_sum_ge_neg_bound v _ _ (M * (2 * n + (j + 1)))
    intro k hk
    have hk' : k.1 + k.2 = n := Finset.mem_antidiagonal.mp hk
    have hk₁ : k.1 ≤ n := by omega
    have hk₂ : k.2 ≤ n := by omega
    have hprod := ord_mul_ge_neg_bounds v _ _
      (M * (2 * k.1 + j)) (M * (2 * k.2 + 1))
      (ih k.1 (fun r hr => hW r (hr.trans hk₁))) (hW k.2 hk₂)
    have he : M * (2 * k.1 + j) + M * (2 * k.2 + 1) =
        M * (2 * n + (j + 1)) := by
      rw [← hk']
      ring
    simpa only [he] using hprod

private theorem ord_coeff_weighted_monomial_ge
    (W : PowerSeries F) (M n s j : ℕ) (c : F)
    (hc : -(M : ℤ) ≤ v.ord c) (hweight : j ≤ 2 * s)
    (hW : ∀ r < n, -((M * (2 * r + 1) : ℕ) : ℤ) ≤
      v.ord (PowerSeries.coeff r W)) :
    -((M * (2 * n + 1) : ℕ) : ℤ) ≤
      v.ord (PowerSeries.coeff n (PowerSeries.C c * PowerSeries.X ^ s * W ^ j)) := by
  by_cases hj : j = 0
  · subst j
    rw [pow_zero, mul_one, PowerSeries.coeff_C_mul_X_pow]
    by_cases hn : n = s
    · rw [ite_eq_left hn]
      have hle : M ≤ M * (2 * n + 1) := by nlinarith
      have hle' : (M : ℤ) ≤ ((M * (2 * n + 1) : ℕ) : ℤ) := by exact_mod_cast hle
      exact (neg_le_neg hle').trans hc
    · rw [ite_eq_right hn, v.ord_zero]
      omega
  have he : PowerSeries.C c * PowerSeries.X ^ s * W ^ j =
      (PowerSeries.C c * W ^ j) * PowerSeries.X ^ s := by ring
  rw [he, PowerSeries.coeff_mul_X_pow']
  by_cases hs : s ≤ n
  · rw [ite_eq_left hs, PowerSeries.coeff_C_mul]
    have hsn : n - s < n := by omega
    have hpow := ord_coeff_pow_ge_weight v W M j (n - s)
      (fun r hr => hW r (hr.trans_lt hsn))
    have hprod := ord_mul_ge_neg_bounds v _ _ M (M * (2 * (n - s) + j)) hc hpow
    have hle : M + M * (2 * (n - s) + j) ≤ M * (2 * n + 1) := by
      have hm := Nat.mul_le_mul_left M
        (show 1 + (2 * (n - s) + j) ≤ 2 * n + 1 by omega)
      nlinarith
    have hle' : ((M + M * (2 * (n - s) + j) : ℕ) : ℤ) ≤
        ((M * (2 * n + 1) : ℕ) : ℤ) := by exact_mod_cast hle
    exact (neg_le_neg hle').trans hprod
  · rw [ite_eq_right hs, v.ord_zero]
    omega

private theorem ord_coeff_weighted_fixed_point_ge
    {ι : Type*} (I : Finset ι) (c : ι → F) (s j : ι → ℕ)
    (hweight : ∀ i ∈ I, j i ≤ 2 * s i) (W : PowerSeries F)
    (hfixed : W = ∑ i ∈ I, PowerSeries.C (c i) * PowerSeries.X ^ s i * W ^ j i)
    (M : ℕ) (hc : ∀ i ∈ I, -(M : ℤ) ≤ v.ord (c i)) (n : ℕ) :
    -((M * (2 * n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n W) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    nth_rw 1 [hfixed]
    rw [map_sum]
    apply ord_finset_sum_ge_neg_bound v _ _ (M * (2 * n + 1))
    intro i hi
    exact ord_coeff_weighted_monomial_ge v W M n (s i) (j i) (c i)
      (hc i hi) (hweight i hi) ih

/-- The finite scalar coefficients of a weighted algebraic equation determine
a linear pole bound for every coefficient of any actual solution. The proof
uses strong induction; no coefficient-growth hypothesis is supplied. -/
theorem weighted_fixed_point_coeff_ord_lower
    {ι : Type*} (I : Finset ι) (c : ι → F) (s j : ι → ℕ)
    (hweight : ∀ i ∈ I, j i ≤ 2 * s i) (W : PowerSeries F)
    (hfixed : W = ∑ i ∈ I, PowerSeries.C (c i) * PowerSeries.X ^ s i * W ^ j i) :
    let M := ∑ i ∈ I, (v.ord (c i)).natAbs
    ∀ n : ℕ, -((M * (2 * n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n W) := by
  intro M n
  apply ord_coeff_weighted_fixed_point_ge v I c s j hweight W hfixed M
  intro i hi
  have hle : (v.ord (c i)).natAbs ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum (fun k _ => Nat.zero_le ((v.ord (c k)).natAbs)) hi
  have hle' : ((v.ord (c i)).natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hle
  have hneg : -v.ord (c i) ≤ ((v.ord (c i)).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -v.ord (c i)))
  omega

end AlgebraicCurve.Place

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

/-- The same finite equation supplies one effective divisor for the coefficient
growth at every place. No divisor or local growth estimates are assumed. -/
theorem exists_weighted_fixed_point_divisor_bound
    {ι : Type*} (I : Finset ι) (c : ι → F) (s j : ι → ℕ)
    (hweight : ∀ i ∈ I, j i ≤ 2 * s i) (W : PowerSeries F)
    (hfixed : W = ∑ i ∈ I, PowerSeries.C (c i) * PowerSeries.X ^ s i * W ^ j i) :
    ∃ D : Modulus K F, ∀ (v : Place K F) (n : ℕ),
      -((D v * (2 * n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n W) := by
  obtain ⟨D, hD, _⟩ := exists_finset_pole_bound (K := K) I c
  refine ⟨D, ?_⟩
  intro v n
  exact Place.ord_coeff_weighted_fixed_point_ge v I c s j hweight W hfixed
    (D v) (hD v) n

end AlgebraicCurve
