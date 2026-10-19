/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.LaurentFormalTranslation

/-! # The sharp coefficient bound for actual Laurent translation

Rescaling the translation variable by the Laurent parameter makes the
translated unit parameter `1 + X`. Its inverse exists already over the
power-series coefficient ring. This gives an actual integral preimage after
extracting the original Laurent order, including for negative orders.
Taking coefficients yields the Hasse bound in every characteristic.
-/

noncomputable section

namespace LaurentSeries

variable {K : Type*} [Field K]

private theorem rescale_C {R : Type*} [CommSemiring R] (a b : R) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C, ↓reduceIte,
      pow_zero, one_mul]
  · simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hn, ↓reduceIte, mul_zero]

private theorem order_coe_nonneg (f : PowerSeries K) :
    0 ≤ (f : LaurentSeries K).order := by
  by_contra h
  have hneg : (f : LaurentSeries K).order < 0 := lt_of_not_ge h
  have hc : (f : LaurentSeries K).coeff (f : LaurentSeries K).order = 0 := by
    simp only [PowerSeries.coeff_coe, hneg, ↓reduceIte]
  have hf := HahnSeries.coeff_order_eq_zero.mp hc
  rw [hf, HahnSeries.order_zero] at hneg
  exact (lt_irrefl 0) hneg

private def scaledTranslation : LaurentSeries K →+* PowerSeries (LaurentSeries K) :=
  (PowerSeries.rescale (HahnSeries.single (1 : ℤ) (1 : K))).comp
    formalTranslation.toRingHom

private theorem scaledTranslation_coe (f : PowerSeries K) :
    scaledTranslation (f : LaurentSeries K) =
      PowerSeries.map (HahnSeries.ofPowerSeries ℤ K)
        (PowerSeries.rescale PowerSeries.X (PowerSeries.formalTranslation f)) := by
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n (PowerSeries.rescale (HahnSeries.single (1 : ℤ) (1 : K))
    (formalTranslation (f : LaurentSeries K))) = _
  rw [PowerSeries.coeff_rescale, coeff_formalTranslation_coe,
    PowerSeries.coeff_map, PowerSeries.coeff_rescale, map_mul, map_pow]
  rw [HahnSeries.ofPowerSeries_X]

private theorem scaledTranslation_parameter :
    scaledTranslation (HahnSeries.single (1 : ℤ) (1 : K)) =
      PowerSeries.C (HahnSeries.single (1 : ℤ) (1 : K)) *
        (1 + PowerSeries.X) := by
  change PowerSeries.rescale _ (formalTranslation _) = _
  rw [formalTranslation_parameter, map_add, rescale_C, PowerSeries.rescale_X,
    mul_add, mul_one]

private theorem exists_scaledTranslation_single_integral (d : ℤ) :
    ∃ W : PowerSeries (PowerSeries K),
      scaledTranslation (HahnSeries.single d (1 : K)) =
        PowerSeries.C (HahnSeries.single d (1 : K)) *
          PowerSeries.map (HahnSeries.ofPowerSeries ℤ K) W := by
  let J := PowerSeries.map (HahnSeries.ofPowerSeries ℤ K)
  let U : PowerSeries (PowerSeries K) := 1 + PowerSeries.X
  have hU : J U = 1 + PowerSeries.X := by
    exact (map_add J 1 PowerSeries.X).trans
      (by rw [map_one, PowerSeries.map_X])
  have hparam : scaledTranslation (HahnSeries.single (1 : ℤ) (1 : K)) =
      PowerSeries.C (HahnSeries.single (1 : ℤ) (1 : K)) * J U := by
    rw [hU]
    exact scaledTranslation_parameter
  have hpos (m : ℕ) :
      scaledTranslation (HahnSeries.single (m : ℤ) (1 : K)) =
        PowerSeries.C (HahnSeries.single (m : ℤ) (1 : K)) * J (U ^ m) := by
    rw [RatFunc.single_one_eq_pow, map_pow, hparam, mul_pow,
      ← map_pow (PowerSeries.C (R := LaurentSeries K)), ← map_pow J,
      ← RatFunc.single_one_eq_pow]
  let V : PowerSeries (PowerSeries K) := PowerSeries.invOfUnit U 1
  have hUV : U * V = 1 := by
    apply PowerSeries.mul_invOfUnit U 1
    change PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries (PowerSeries K)) = 1
    rw [map_add, map_one, PowerSeries.constantCoeff_X, add_zero]
  have hneg (m : ℕ) :
      scaledTranslation (HahnSeries.single (-(m : ℤ)) (1 : K)) =
        PowerSeries.C (HahnSeries.single (-(m : ℤ)) (1 : K)) * J (V ^ m) := by
    have hm : HahnSeries.single (m : ℤ) (1 : K) *
        HahnSeries.single (-(m : ℤ)) (1 : K) = 1 := by
      rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one,
        HahnSeries.single_zero_one]
    have hleft : scaledTranslation (HahnSeries.single (m : ℤ) (1 : K)) *
        scaledTranslation (HahnSeries.single (-(m : ℤ)) (1 : K)) = 1 := by
      rw [← map_mul, hm, map_one]
    have hright : scaledTranslation (HahnSeries.single (m : ℤ) (1 : K)) *
        (PowerSeries.C (HahnSeries.single (-(m : ℤ)) (1 : K)) * J (V ^ m)) = 1 := by
      rw [hpos, mul_mul_mul_comm,
        ← map_mul (PowerSeries.C (R := LaurentSeries K)), ← map_mul J,
        ← mul_pow, hm, hUV, one_pow, map_one, map_one, mul_one]
    have hm0 : scaledTranslation (HahnSeries.single (m : ℤ) (1 : K)) ≠ 0 := by
      intro h
      have hzero := (scaledTranslation (K := K)).injective (h.trans (map_zero _).symm)
      exact HahnSeries.single_ne_zero one_ne_zero hzero
    exact mul_left_cancel₀ hm0 (hleft.trans hright.symm)
  cases d with
  | ofNat m => exact ⟨U ^ m, hpos m⟩
  | negSucc m => exact ⟨V ^ (m + 1), hneg (m + 1)⟩

/-- After scaling the translation variable by the local parameter, the
entire translated Laurent series has an integral coefficient preimage once
its original order is extracted. This includes all negative orders. -/
theorem exists_scaled_formalTranslation_integral (f : LaurentSeries K) :
    ∃ W : PowerSeries (PowerSeries K),
      PowerSeries.rescale (HahnSeries.single (1 : ℤ) (1 : K)) (formalTranslation f) =
        PowerSeries.C (HahnSeries.single f.order (1 : K)) *
          PowerSeries.map (HahnSeries.ofPowerSeries ℤ K) W := by
  obtain ⟨W, hW⟩ := exists_scaledTranslation_single_integral (K := K) f.order
  let B := PowerSeries.rescale PowerSeries.X
    (PowerSeries.formalTranslation f.powerSeriesPart)
  refine ⟨W * B, ?_⟩
  change scaledTranslation f = _
  calc
    scaledTranslation f = scaledTranslation
        (HahnSeries.single f.order (1 : K) * (f.powerSeriesPart : LaurentSeries K)) :=
      congrArg scaledTranslation f.single_order_mul_powerSeriesPart.symm
    _ = scaledTranslation (HahnSeries.single f.order (1 : K)) *
        scaledTranslation (f.powerSeriesPart : LaurentSeries K) := map_mul _ _ _
    _ = (PowerSeries.C (HahnSeries.single f.order (1 : K)) *
        PowerSeries.map (HahnSeries.ofPowerSeries ℤ K) W) *
          PowerSeries.map (HahnSeries.ofPowerSeries ℤ K) B := by
      rw [hW, scaledTranslation_coe]
    _ = _ := by rw [map_mul, mul_assoc]

/-- Each nonzero coefficient of the actual Laurent translation has order
at least the original order minus its coefficient index. -/
theorem order_coeff_formalTranslation_ge (f : LaurentSeries K) (n : ℕ)
    (hn : PowerSeries.coeff n (formalTranslation f) ≠ 0) :
    f.order - (n : ℤ) ≤ (PowerSeries.coeff n (formalTranslation f)).order := by
  obtain ⟨W, hW⟩ := exists_scaled_formalTranslation_integral f
  have hc := congrArg (PowerSeries.coeff n) hW
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, PowerSeries.coeff_map] at hc
  have hr : (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hWn : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.coeff n W)) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact (mul_ne_zero (pow_ne_zero n hr) hn) hc
  have ho := congrArg HahnSeries.order hc
  rw [HahnSeries.order_mul (pow_ne_zero n hr) hn,
    HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero) hWn,
    HahnSeries.order_pow, HahnSeries.order_single one_ne_zero,
    HahnSeries.order_single one_ne_zero, nsmul_eq_mul, mul_one] at ho
  have hnonneg := order_coe_nonneg (PowerSeries.coeff n W)
  omega

/-- The actual formal difference is centered in its translation parameter. -/
theorem constantCoeff_formalTranslation_sub_C (f : LaurentSeries K) :
    PowerSeries.constantCoeff (formalTranslation f - PowerSeries.C f) = 0 := by
  rw [map_sub, constantCoeff_formalTranslation, PowerSeries.constantCoeff_C, sub_self]

/-- Removing the constant coefficient preserves the sharp positive-degree
order bound. -/
theorem order_coeff_formalTranslation_sub_C_ge (f : LaurentSeries K) (n : ℕ)
    (hn : 0 < n)
    (hc : PowerSeries.coeff n (formalTranslation f - PowerSeries.C f) ≠ 0) :
    f.order - (n : ℤ) ≤
      (PowerSeries.coeff n (formalTranslation f - PowerSeries.C f)).order := by
  have heq : PowerSeries.coeff n (formalTranslation f - PowerSeries.C f) =
      PowerSeries.coeff n (formalTranslation f) := by
    rw [map_sub, PowerSeries.coeff_C, ite_eq_right (Nat.ne_of_gt hn), sub_zero]
  rw [heq] at hc ⊢
  exact order_coeff_formalTranslation_ge f n hc

end LaurentSeries
