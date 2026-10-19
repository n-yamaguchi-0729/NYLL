/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Degree.FormalRootPoleBound
import Nyll.SchemeTheory.RingTheory.Henselian.FormalSimpleRoot
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Effective divisor bounds for actual simple algebraic formal roots

For a polynomial with a simple root at the origin, its actual formal root
has linearly bounded coefficient poles. The weighted equation is derived
from the polynomial by removing its nonzero linear term and writing the
root as `X * W`; it is not an additional hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem exists_weighted_equation_of_simple_root
    (P : Polynomial (Polynomial F))
    (hzero : (P.coeff 0).coeff 0 = 0) (hu : (P.coeff 1).coeff 0 ≠ 0)
    (Z : PowerSeries F) (hZ : PowerSeries.constantCoeff Z = 0)
    (hroot : (P.map Polynomial.coeToPowerSeries.ringHom).eval Z = 0) :
    ∃ (W : PowerSeries F) (I : Finset (Σ _ : ℕ, ℕ)) (c : (Σ _ : ℕ, ℕ) → F),
      Z = PowerSeries.X * W ∧
      (∀ k ∈ I, k.1 ≤ 2 * (k.2 + k.1 - 1)) ∧
      W = ∑ k ∈ I, PowerSeries.C (c k) *
        PowerSeries.X ^ (k.2 + k.1 - 1) * W ^ k.1 := by
  classical
  let W := PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) Z)
  have hZW : Z = PowerSeries.X * W := by
    simpa only [hZ, map_zero, add_zero] using PowerSeries.eq_X_mul_shift_add_const Z
  let J : Finset (Σ _ : ℕ, ℕ) := P.support.sigma (fun j => (P.coeff j).support)
  let c₀ : (Σ _ : ℕ, ℕ) → F := fun k => (P.coeff k.1).coeff k.2
  let e : Σ _ : ℕ, ℕ := ⟨1, 0⟩
  let u := (P.coeff 1).coeff 0
  let I := J.erase e
  let c : (Σ _ : ℕ, ℕ) → F := fun k => -u⁻¹ * c₀ k
  have he : e ∈ J := by
    apply Finset.mem_sigma.mpr
    constructor
    · apply Polynomial.mem_support_iff.mpr
      intro hP1
      apply hu
      rw [hP1, Polynomial.coeff_zero]
    · exact Polynomial.mem_support_iff.mpr hu
  have hpos (k : Σ _ : ℕ, ℕ) (hk : k ∈ J) : 1 ≤ k.2 + k.1 := by
    have hcoeff := Polynomial.mem_support_iff.mp (Finset.mem_sigma.mp hk).2
    by_contra hn
    have hk₁ : k.1 = 0 := by omega
    have hk₂ : k.2 = 0 := by omega
    exact hcoeff (by rw [hk₁, hk₂, hzero])
  have hcoeff (R : Polynomial F) : (R : PowerSeries F) =
      ∑ i ∈ R.support, PowerSeries.C (R.coeff i) * PowerSeries.X ^ i := by
    have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := F))
      R.as_sum_support_C_mul_X_pow
    simpa only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X] using h
  have heval : (P.map Polynomial.coeToPowerSeries.ringHom).eval Z =
      ∑ k ∈ J, PowerSeries.C (c₀ k) * PowerSeries.X ^ k.2 * Z ^ k.1 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    dsimp only [J]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    change (P.coeff j : PowerSeries F) * Z ^ j = _
    rw [hcoeff, Finset.sum_mul]
  let b : (Σ _ : ℕ, ℕ) → PowerSeries F := fun k =>
    PowerSeries.C (c₀ k) * PowerSeries.X ^ (k.2 + k.1 - 1) * W ^ k.1
  have hterm (k : Σ _ : ℕ, ℕ) (hk : k ∈ J) :
      PowerSeries.C (c₀ k) * PowerSeries.X ^ k.2 * Z ^ k.1 = PowerSeries.X * b k := by
    rw [hZW, mul_pow]
    have hp : k.2 + k.1 - 1 + 1 = k.2 + k.1 := by have := hpos k hk; omega
    change PowerSeries.C (c₀ k) * PowerSeries.X ^ k.2 *
        (PowerSeries.X ^ k.1 * W ^ k.1) =
      PowerSeries.X * (PowerSeries.C (c₀ k) *
        PowerSeries.X ^ (k.2 + k.1 - 1) * W ^ k.1)
    calc
      _ = PowerSeries.C (c₀ k) * PowerSeries.X ^ (k.2 + k.1) * W ^ k.1 := by
        rw [pow_add]
        ring
      _ = _ := by
        nth_rw 1 [← hp]
        rw [pow_succ]
        ring
  have hsum : ∑ k ∈ J, b k = 0 := by
    have hxsum : PowerSeries.X * (∑ k ∈ J, b k) = 0 := by
      rw [Finset.mul_sum]
      calc
        _ = ∑ k ∈ J, PowerSeries.C (c₀ k) * PowerSeries.X ^ k.2 * Z ^ k.1 :=
          Finset.sum_congr rfl (fun k hk => (hterm k hk).symm)
        _ = 0 := heval.symm.trans hroot
    exact (mul_eq_zero.mp hxsum).resolve_left PowerSeries.X_ne_zero
  have hbe : b e = PowerSeries.C u * W := by
    simp only [b, e, c₀, u, zero_add, Nat.sub_self, pow_zero, pow_one, mul_one]
  have hlin : PowerSeries.C u * W + ∑ k ∈ I, b k = 0 := by
    rw [← hbe, Finset.add_sum_erase J b he]
    exact hsum
  have hscaled : W = -(PowerSeries.C u⁻¹ * ∑ k ∈ I, b k) := by
    have h := congrArg (fun A : PowerSeries F => PowerSeries.C u⁻¹ * A)
      (eq_neg_of_add_eq_zero_left hlin)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul, mul_neg] at h
    exact h
  refine ⟨W, I, c, hZW, ?_, ?_⟩
  · intro k hk
    obtain ⟨hkne, hkJ⟩ := Finset.mem_erase.mp hk
    have hp := hpos k hkJ
    rcases k with ⟨j, i⟩
    have hneq : ¬(j = 1 ∧ i = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hkne rfl
    change j ≤ 2 * (i + j - 1)
    dsimp only at hp
    omega
  · calc
      W = -(PowerSeries.C u⁻¹ * ∑ k ∈ I, b k) := hscaled
      _ = ∑ k ∈ I, -(PowerSeries.C u⁻¹ * b k) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [b, c]
        rw [map_mul, map_neg]
        ring

variable [HasPrincipalDivisors K F]

/-- Every actual simple formal root of finite polynomial data has one
effective divisor bounding all positive-degree coefficients. The bound is
constructed from the polynomial and the inverse of its linear coefficient. -/
theorem exists_simple_polynomial_root_divisor_bound
    (P : Polynomial (Polynomial F))
    (hzero : (P.coeff 0).coeff 0 = 0) (hu : (P.coeff 1).coeff 0 ≠ 0)
    (Z : PowerSeries F) (hZ : PowerSeries.constantCoeff Z = 0)
    (hroot : (P.map Polynomial.coeToPowerSeries.ringHom).eval Z = 0) :
    ∃ D : Modulus K F, ∀ (v : Place K F) (n : ℕ),
      -((D v * (2 * n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff (n + 1) Z) := by
  obtain ⟨W, I, c, hZW, hweight, hfixed⟩ :=
    exists_weighted_equation_of_simple_root P hzero hu Z hZ hroot
  obtain ⟨D, hD⟩ := exists_weighted_fixed_point_divisor_bound (K := K) I c
    (fun k => k.2 + k.1 - 1) (fun k => k.1) hweight W hfixed
  refine ⟨D, ?_⟩
  intro v n
  rw [hZW, ← pow_one (PowerSeries.X : PowerSeries F), PowerSeries.coeff_X_pow_mul]
  exact hD v n

/-- A monic polynomial with a simple root at the origin supplies both its
actual formal root and an effective divisor controlling that root's coefficients. -/
theorem exists_monic_simple_root_with_divisor_bound
    (P : Polynomial (Polynomial F)) (hP : P.Monic)
    (hzero : (P.coeff 0).coeff 0 = 0) (hu : (P.coeff 1).coeff 0 ≠ 0) :
    ∃ (Z : PowerSeries F) (D : Modulus K F),
      (P.map Polynomial.coeToPowerSeries.ringHom).eval Z = 0 ∧
      PowerSeries.constantCoeff Z = 0 ∧
      ∀ (v : Place K F) (n : ℕ),
        -((D v * (2 * n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff (n + 1) Z) := by
  let ρ : Polynomial F →+* PowerSeries F := Polynomial.coeToPowerSeries.ringHom
  have hconstant : ((P.map ρ).map PowerSeries.constantCoeff).eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, Polynomial.coeff_map]
    exact hzero
  have hder : ((P.map ρ).map PowerSeries.constantCoeff).derivative.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, zero_add,
      Nat.cast_zero, zero_add, mul_one, Polynomial.coeff_map, Polynomial.coeff_map]
    exact hu
  obtain ⟨Z, ⟨hroot, hZ⟩, _⟩ := PowerSeries.existsUnique_monic_root_of_constantCoeff
    (P.map ρ) (hP.map ρ) 0 hconstant hder
  obtain ⟨D, hD⟩ := exists_simple_polynomial_root_divisor_bound (K := K) P hzero hu Z hZ hroot
  exact ⟨Z, D, hroot, hZ, hD⟩

end AlgebraicCurve
