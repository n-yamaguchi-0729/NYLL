/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalDiagonalEvaluation
import Nyll.AlgebraicCurves.Divisors.Degree.FormalTranslationDivisorBound
import Nyll.AlgebraicCurves.Divisors.Degree.PowerSeriesPoleOperations

/-! # Pole bounds on the actual generic formal diagonal

Finite tensors and localization fractions, with the actual inverse-series
recurrence, supply a linear pole bound for every evaluated local function.
No growth estimate or local-ring evaluation is assumed as extra data.
-/

noncomputable section

open scoped TensorProduct BigOperators

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable [HasPrincipalDivisors K F]

private theorem exists_constant_series_divisor_bound (q : F) :
    ∃ D : Modulus K F, ∀ (v : Place K F) (n : ℕ),
      -((D v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (PowerSeries.C q)) := by
  obtain ⟨D, hD, _⟩ := exists_finset_pole_bound (K := K)
    (Finset.univ : Finset Unit) (fun _ : Unit => q)
  refine ⟨D, ?_⟩
  intro v n
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.zero_add, Nat.mul_one, PowerSeries.coeff_zero_C] using
      hD v () (Finset.mem_univ ())
  · rw [PowerSeries.coeff_C_of_ne_zero hn, v.ord_zero]
    omega

/-- Finite tensor expressions have linearly bounded coefficients under the
actual translated/constant evaluation. -/
theorem exists_formalDiagonalTensorMap_divisor_bound
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (r : F ⊗[K] F) :
    ∃ D : Modulus K F, ∀ (v : Place K F) (n : ℕ),
      -((D v * (n + 1) : ℕ) : ℤ) ≤
        v.ord (PowerSeries.coeff n (PowerSeries.diagonalTensorMap σ r)) := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨D₁, hD₁⟩ := exists_formalTranslation_divisor_bound
      (K := K) t ht σ hσt hσ0 a
    obtain ⟨D₂, hD₂⟩ := exists_constant_series_divisor_bound (K := K) b
    exact exists_powerSeries_mul_linear_pole_bound (σ a) (PowerSeries.C b)
      D₁ D₂ hD₁ hD₂
  | add a b ha hb =>
    obtain ⟨D₁, hD₁⟩ := ha
    obtain ⟨D₂, hD₂⟩ := hb
    refine ⟨D₁ + D₂, ?_⟩
    intro v n
    let A := PowerSeries.coeff n (PowerSeries.diagonalTensorMap σ a)
    let B := PowerSeries.coeff n (PowerSeries.diagonalTensorMap σ b)
    have hA : -(((D₁ v + D₂ v) * (n + 1) : ℕ) : ℤ) ≤ v.ord A := by
      apply le_trans _ (hD₁ v n)
      exact neg_le_neg (Int.ofNat_le.mpr
        (Nat.mul_le_mul_right (n + 1) (Nat.le_add_right _ _)))
    have hB : -(((D₁ v + D₂ v) * (n + 1) : ℕ) : ℤ) ≤ v.ord B := by
      apply le_trans _ (hD₂ v n)
      exact neg_le_neg (Int.ofNat_le.mpr
        (Nat.mul_le_mul_right (n + 1) (Nat.le_add_left _ _)))
    have hs := v.ord_finset_sum_ge_neg_bound ({false, true} : Finset Bool)
      (fun i => Bool.rec A B i) ((D₁ v + D₂ v) * (n + 1))
      (fun i _ => by
        cases i with
        | false => exact hA
        | true => exact hB)
    simpa only [Finset.sum_pair (by decide : false ≠ true),
      Finsupp.add_apply, map_add] using hs

/-- Every actual local function at the generic diagonal has a linear
coefficient-pole bound. Localization denominators are inverted only after
their nonzero constant term has been proved from the diagonal prime. -/
theorem exists_formalDiagonalEvaluation_divisor_bound
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (z : Localization.AtPrime (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal) :
    ∃ D : Modulus K F, ∀ (v : Place K F) (n : ℕ),
      -((D v * (n + 1) : ℕ) : ℤ) ≤
        v.ord (PowerSeries.coeff n (PowerSeries.diagonalEvaluation σ hσ0 z)) := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal.primeCompl z
  have hunit := PowerSeries.isUnit_diagonalTensorMap σ hσ0 s
  have hnonzero : PowerSeries.constantCoeff (PowerSeries.diagonalTensorMap σ s) ≠ 0 :=
    isUnit_iff_ne_zero.mp (PowerSeries.isUnit_iff_constantCoeff.mp hunit)
  have hvalue : PowerSeries.diagonalEvaluation σ hσ0 (IsLocalization.mk' _ a s) =
      PowerSeries.diagonalTensorMap σ a * (PowerSeries.diagonalTensorMap σ s)⁻¹ := by
    apply (IsLocalization.lift_mk'_spec (PowerSeries.isUnit_diagonalTensorMap σ hσ0) a _ s).mpr
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    symm
    calc
      _ = PowerSeries.diagonalTensorMap σ a *
          (PowerSeries.diagonalTensorMap σ s * (PowerSeries.diagonalTensorMap σ s)⁻¹) := by ring
      _ = _ := by rw [PowerSeries.mul_inv_cancel _ hnonzero, mul_one]
  obtain ⟨D₁, hD₁⟩ := exists_formalDiagonalTensorMap_divisor_bound
    t ht σ hσt hσ0 a
  obtain ⟨D₂, hD₂⟩ := exists_formalDiagonalTensorMap_divisor_bound
    t ht σ hσt hσ0 s
  obtain ⟨D₃, _, hD₃⟩ := exists_powerSeries_inv_linear_pole_bound
    (PowerSeries.diagonalTensorMap σ s) hunit D₂ hD₂
  rw [hvalue]
  exact exists_powerSeries_mul_linear_pole_bound
    (PowerSeries.diagonalTensorMap σ a) (PowerSeries.diagonalTensorMap σ s)⁻¹ D₁ D₃ hD₁ hD₃

end AlgebraicCurve
