/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Orders.RationalSeriesPoleBound
import Nyll.AlgebraicCurves.Divisors.Degree.FiniteTypePoleBound
import Mathlib.Data.Int.Lemmas

/-! # One effective divisor for finite rational formal expansions

The finite numerator and denominator coefficients, together with their
inverses, supply an actual effective divisor. A fixed multiple of it controls
every series coefficient at every place, with growth linear in the coefficient
index. Neither a uniform divisor nor any coefficient estimate is assumed.

This concerns formal quotients of finite polynomial data. Realizing arbitrary
curve coordinates along the formal diagonal, and the subsequent global
reciprocity argument, are separate steps not asserted here.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [HasPrincipalDivisors K F]

private theorem exists_finset_abs_order_bound (S : Finset F) :
    ∃ D : Modulus K F, ∀ v : Place K F, ∀ a ∈ S, (v.ord a).natAbs ≤ D v := by
  classical
  obtain ⟨D, hD, _⟩ := exists_finset_pole_bound (K := K)
    (S ∪ S.image (fun a : F => a⁻¹)) (fun a => a)
  refine ⟨D, ?_⟩
  intro v a ha
  have hlo := hD v a (Finset.mem_union_left _ ha)
  have hhi := hD v a⁻¹ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
  rw [v.ord_inv] at hhi
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  exact abs_le.mpr ⟨hlo, by omega⟩

/-- Finitely many actual rational formal expansions have one effective
divisor bounding all their coefficients. The multiplier is determined by
the finite numerator and denominator supports, independently of the place
and coefficient index. The original denominator equations are retained. -/
theorem exists_polynomial_quotient_family_divisor_bound
    {ι : Type*} [Finite ι] (P Q : ι → Polynomial F)
    (hQ : ∀ i, (Q i).coeff 0 ≠ 0) :
    ∃ D : Modulus K F, ∀ i,
      let S := (P i : PowerSeries F) * (Q i : PowerSeries F)⁻¹
      S * (Q i : PowerSeries F) = (P i : PowerSeries F) ∧
        ∀ (v : Place K F) (n : ℕ),
          -(((n + 1) * D v : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n S) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let A : Finset F := Finset.univ.biUnion fun i =>
    (P i).support.image (P i).coeff ∪ (Q i).support.image (Q i).coeff
  obtain ⟨D₀, hD₀⟩ := exists_finset_abs_order_bound (K := K) A
  have hB (v : Place K F) (R : Polynomial F)
      (hR : ∀ j ∈ R.support, R.coeff j ∈ A) :
      v.polynomialOrderBound R ≤ R.support.card * D₀ v := by
    change (∑ j ∈ R.support, (v.ord (R.coeff j)).natAbs) ≤ _
    calc
      _ ≤ ∑ _j ∈ R.support, D₀ v :=
        Finset.sum_le_sum (fun j hj => hD₀ v (R.coeff j) (hR j hj))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hP (v : Place K F) (i : ι) :
      v.polynomialOrderBound (P i) ≤ (P i).support.card * D₀ v := by
    apply hB
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)⟩
  have hQ' (v : Place K F) (i : ι) :
      v.polynomialOrderBound (Q i) ≤ (Q i).support.card * D₀ v := by
    apply hB
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)⟩
  let c : ℕ := ∑ i, ((P i).support.card + 2 * (Q i).support.card)
  let D : Modulus K F := c • D₀
  have hDv (v : Place K F) : D v = c * D₀ v := by
    simp only [D, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_id]
  have hc (i : ι) : (P i).support.card + 2 * (Q i).support.card ≤ c := by
    dsimp only [c]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le
      ((P j).support.card + 2 * (Q j).support.card)) (Finset.mem_univ i)
  refine ⟨D, ?_⟩
  intro i S
  constructor
  · change ((P i : PowerSeries F) * (Q i : PowerSeries F)⁻¹) *
      (Q i : PowerSeries F) = _
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
      simpa only [Polynomial.constantCoeff_coe] using hQ i), mul_one]
  · intro v n
    have hb : v.polynomialOrderBound (P i) + 2 * v.polynomialOrderBound (Q i) ≤ D v := by
      rw [hDv]
      calc
        _ ≤ (P i).support.card * D₀ v + 2 * ((Q i).support.card * D₀ v) :=
          Nat.add_le_add (hP v i) (Nat.mul_le_mul_left 2 (hQ' v i))
        _ = ((P i).support.card + 2 * (Q i).support.card) * D₀ v := by ring
        _ ≤ c * D₀ v := Nat.mul_le_mul_right _ (hc i)
    have hbound := ((v.polynomial_quotient_linear_pole_bound (P i) (Q i) (hQ i)).2 n)
    have hle :
        (((v.polynomialOrderBound (P i) + 2 * v.polynomialOrderBound (Q i)) *
          (n + 1) : ℕ) : ℤ) ≤ (((n + 1) * D v : ℕ) : ℤ) := by
      have hn := Nat.mul_le_mul_right (n + 1) hb
      rw [Nat.mul_comm (D v) (n + 1)] at hn
      exact_mod_cast hn
    exact (neg_le_neg hle).trans hbound

end AlgebraicCurve
