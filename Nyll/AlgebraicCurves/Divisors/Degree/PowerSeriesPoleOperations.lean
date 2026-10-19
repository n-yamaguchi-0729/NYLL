/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Orders.RationalSeriesPoleBound
import Nyll.AlgebraicCurves.Divisors.Degree.FiniteTypePoleBound
import Mathlib.Tactic.Linarith

/-! # Products and inverses of series with linear pole bounds

Coefficient convolution preserves a linear bound with divisor `D_A + D_B`.
The actual inverse recurrence gives the sharper local bound
`-((2a + b) * n + b)`, where `b` bounds the pole of the inverse constant term.
Finite support of principal divisors constructs such a `b` globally, so the
inverse of a unit series has a linear bound with divisor `2D_A + D₀`.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

/-- Coefficient convolution adds the two linear pole constants. -/
theorem powerSeries_mul_coeff_ord_lower (v : Place K F)
    (A B : PowerSeries F) (a b : ℕ)
    (hA : ∀ n, -((a * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A))
    (hB : ∀ n, -((b * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n B))
    (n : ℕ) :
    -(((a + b) * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (A * B)) := by
  rw [PowerSeries.coeff_mul]
  apply v.ord_finset_sum_ge_neg_bound _ _ ((a + b) * (n + 1))
  intro x hx
  have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
  have hprod := v.ord_mul_ge_neg_bounds _ _ (a * (x.1 + 1)) (b * (x.2 + 1))
    (hA x.1) (hB x.2)
  have hle : a * (x.1 + 1) + b * (x.2 + 1) ≤ (a + b) * (n + 1) := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left a (by omega))
      (Nat.mul_le_mul_left b (by omega))
  exact (neg_le_neg (Int.ofNat_le.mpr hle)).trans hprod

/-- The actual inverse recursion gives a linear pole estimate. The constant
`b` bounds only the inverse constant term, not any unknown inverse coefficient. -/
theorem powerSeries_inv_coeff_ord_lower (v : Place K F)
    (A : PowerSeries F) (a b : ℕ)
    (hA : ∀ n, -((a * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A))
    (hconstant : -(b : ℤ) ≤ v.ord ((PowerSeries.constantCoeff A)⁻¹)) (n : ℕ) :
    -(((2 * a + b) * n + b : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A⁻¹) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [PowerSeries.coeff_inv, ite_eq_left rfl]
      simpa only [Nat.mul_zero, Nat.zero_add] using hconstant
    rw [PowerSeries.coeff_inv, ite_eq_right hn]
    have hc : -(b : ℤ) ≤ v.ord (-(PowerSeries.constantCoeff A)⁻¹) := by
      simpa only [Place.ord, Valuation.map_neg] using hconstant
    have hs : -(((2 * a + b) * n : ℕ) : ℤ) ≤
        v.ord (∑ x ∈ Finset.antidiagonal n,
          if x.2 < n then PowerSeries.coeff x.1 A * PowerSeries.coeff x.2 A⁻¹ else 0) := by
      apply v.ord_finset_sum_ge_neg_bound _ _ ((2 * a + b) * n)
      intro x hx
      have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
      by_cases hxlt : x.2 < n
      · rw [ite_eq_left hxlt]
        have hprod := v.ord_mul_ge_neg_bounds _ _ (a * (x.1 + 1))
          ((2 * a + b) * x.2 + b) (hA x.1) (ih x.2 hxlt)
        have hle : a * (x.1 + 1) + ((2 * a + b) * x.2 + b) ≤
            (2 * a + b) * n := by
          have hi : 1 ≤ x.1 := by omega
          have hm := Nat.mul_le_mul_left (a + b) hi
          rw [← hxsum]
          nlinarith
        exact (neg_le_neg (Int.ofNat_le.mpr hle)).trans hprod
      · rw [ite_eq_right hxlt, v.ord_zero]
        omega
    have hprod := v.ord_mul_ge_neg_bounds _ _ b ((2 * a + b) * n) hc hs
    have he : b + (2 * a + b) * n = (2 * a + b) * n + b := Nat.add_comm _ _
    simpa only [he] using hprod

end Place

/-- Two actual finite divisors controlling the input coefficients construct
one divisor controlling every coefficient of the product. -/
theorem exists_powerSeries_mul_linear_pole_bound
    (A B : PowerSeries F) (D_A D_B : Modulus K F)
    (hA : ∀ (v : Place K F) (n : ℕ),
      -((D_A v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A))
    (hB : ∀ (v : Place K F) (n : ℕ),
      -((D_B v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n B)) :
    ∃ D : Modulus K F, ∀ (v : Place K F) (n : ℕ),
      -((D v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (A * B)) := by
  refine ⟨D_A + D_B, ?_⟩
  intro v n
  simpa only [Finsupp.add_apply] using
    v.powerSeries_mul_coeff_ord_lower A B (D_A v) (D_B v) (hA v) (hB v) n

variable [HasPrincipalDivisors K F]

/-- A unit series with linearly bounded coefficient poles has an actual
inverse with the same kind of finite divisor bound. The extra divisor is
constructed from the single rational function given by its inverse constant term. -/
theorem exists_powerSeries_inv_linear_pole_bound
    (A : PowerSeries F) (hunit : IsUnit A) (D_A : Modulus K F)
    (hA : ∀ (v : Place K F) (n : ℕ),
      -((D_A v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A)) :
    ∃ D : Modulus K F, A * A⁻¹ = 1 ∧
      ∀ (v : Place K F) (n : ℕ),
        -((D v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n A⁻¹) := by
  classical
  obtain ⟨D₀, hconstant, _⟩ := exists_finset_pole_bound (K := K)
    (Finset.univ : Finset Unit) (fun _ : Unit => (PowerSeries.constantCoeff A)⁻¹)
  have hA0 : PowerSeries.constantCoeff A ≠ 0 :=
    isUnit_iff_ne_zero.mp (PowerSeries.isUnit_iff_constantCoeff.mp hunit)
  refine ⟨D_A + D_A + D₀, PowerSeries.mul_inv_cancel A hA0, ?_⟩
  intro v n
  have h := v.powerSeries_inv_coeff_ord_lower A (D_A v) (D₀ v) (hA v)
    (hconstant v () (Finset.mem_univ ())) n
  have hle : (2 * D_A v + D₀ v) * n + D₀ v ≤
      (D_A v + D_A v + D₀ v) * (n + 1) := by
    nlinarith
  simp only [Finsupp.add_apply]
  exact (neg_le_neg (Int.ofNat_le.mpr hle)).trans h

end AlgebraicCurve
