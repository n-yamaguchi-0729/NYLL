/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalSimpleRoot

/-! # Tame inverse roots of the formal translation factor

When the ramification exponent is invertible, Hensel's theorem constructs the
unique series `B` with constant term one and `B^e (1 + X) = 1`. This construction
works in positive characteristic without dividing by factorials. Rescaling
then gives the actual tame parameter change over any coefficient extension.
-/

noncomputable section

namespace PowerSeries

variable {K : Type*} [Field K]

/-- The tame inverse root exists uniquely in every characteristic in which
the exponent is nonzero. -/
theorem existsUnique_tameInverseRoot (e : ℕ) (he : (e : K) ≠ 0) :
    ∃! B : PowerSeries K, constantCoeff B = 1 ∧ B ^ e * (1 + X) = 1 := by
  have he0 : e ≠ 0 := by
    intro h
    exact he (h ▸ Nat.cast_zero)
  let P : Polynomial (PowerSeries K) :=
    Polynomial.X ^ e - Polynomial.C ((1 + X)⁻¹)
  have hP : P.Monic := Polynomial.monic_X_pow_sub_C _ he0
  have hmap : P.map constantCoeff = Polynomial.X ^ e - Polynomial.C (1 : K) := by
    simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, constantCoeff_inv, map_add, map_one, constantCoeff_X,
      add_zero, inv_one]
  have hroot : (P.map constantCoeff).eval 1 = 0 := by
    rw [hmap, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, one_pow, sub_self]
  have hder : (P.map constantCoeff).derivative.eval 1 ≠ 0 := by
    rw [hmap, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
    exact he
  have hunit : constantCoeff (1 + (X : PowerSeries K)) ≠ 0 := by
    rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero
  obtain ⟨B, hB, huniq⟩ := existsUnique_monic_root_of_constantCoeff P hP 1 hroot hder
  have hpow : B ^ e = (1 + X)⁻¹ := by
    apply sub_eq_zero.mp
    simpa only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] using hB.1
  refine ⟨B, ⟨hB.2, ?_⟩, ?_⟩
  · rw [hpow]
    exact PowerSeries.inv_mul_cancel _ hunit
  · intro A hA
    apply huniq A
    refine ⟨?_, hA.1⟩
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    apply sub_eq_zero.mpr
    calc
      A ^ e = (A ^ e * (1 + X)) * (1 + X)⁻¹ := by
        rw [mul_assoc, PowerSeries.mul_inv_cancel _ hunit, mul_one]
      _ = (1 + X)⁻¹ := by rw [hA.2, one_mul]

/-- The actual rescaled tame root, with its equation after scalar extension. -/
theorem exists_tameParameterChange (e : ℕ) (he : (e : K) ≠ 0)
    {R : Type*} [CommRing R] [Algebra K R] (t : R) :
    ∃ B : PowerSeries K, constantCoeff B = 1 ∧ B ^ e * (1 + X) = 1 ∧
      let S := C t * rescale (t ^ e) (map (algebraMap K R) B)
      constantCoeff S = t ∧ S ^ e * (1 + C (t ^ e) * X) = C (t ^ e) := by
  obtain ⟨B, hB, _⟩ := existsUnique_tameInverseRoot e he
  refine ⟨B, hB.1, hB.2, ?_⟩
  intro S
  have hrescale : constantCoeff (rescale (t ^ e) (map (algebraMap K R) B)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_map, coeff_zero_eq_constantCoeff_apply, hB.1, map_one]
  have hscaled : (rescale (t ^ e) (map (algebraMap K R) B)) ^ e *
      (1 + C (t ^ e) * X) = 1 := by
    have h := congrArg (fun A : PowerSeries K =>
      rescale (t ^ e) (map (algebraMap K R) A)) hB.2
    simpa only [map_mul, map_pow, map_add, map_one, map_X, rescale_X] using h
  constructor
  · change constantCoeff (C t * _) = t
    rw [map_mul, constantCoeff_C, hrescale, mul_one]
  · change (C t * _) ^ e * _ = _
    rw [mul_pow, ← map_pow, mul_assoc, hscaled, mul_one]

end PowerSeries
