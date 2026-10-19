/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.FormalTranslationSimplePolynomial
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveFormalTranslation
import Nyll.AlgebraicCurves.Divisors.Degree.SimpleRootPolynomialDivisorBound
import Nyll.AlgebraicCurves.Divisors.Degree.FiniteTypePoleBound

/-! # Effective divisor bounds for actual curve-field formal translations

The separating minimal polynomial supplies a finite simple-root equation
for each translated function. Its weighted coefficient estimate and the
pole divisor of the constant term give a linear bound at every place.
A finite family of coordinates has one common effective divisor.

Both the formal translation and the divisor are constructed from the
curve-field data; no formal lift or coefficient-growth estimate is assumed
in the final existence theorem. Global reciprocity is a separate step.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [HasPrincipalDivisors K F]

/-- Each actual translated function has one effective divisor controlling
all coefficients, including the constant coefficient. The polynomial and
the divisor are constructed from the given finite separable extension. -/
theorem exists_formalTranslation_divisor_bound
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F) (q : F) :
    ∃ D : Modulus K F, ∀ (v : Place K F) (n : ℕ),
      -((D v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (σ q)) := by
  obtain ⟨P, hP0, hP1, hPq⟩ :=
    exists_formalTranslation_simple_polynomial t ht σ hσt hσ0 q
  have hq0 : PowerSeries.constantCoeff (σ q) = q := RingHom.congr_fun hσ0 q
  have hZ0 : PowerSeries.constantCoeff (σ q - PowerSeries.C q) = 0 := by
    rw [map_sub, hq0, PowerSeries.constantCoeff_C, sub_self]
  obtain ⟨D₁, hD₁⟩ := exists_simple_polynomial_root_divisor_bound (K := K)
    P hP0 hP1 (σ q - PowerSeries.C q) hZ0 hPq
  obtain ⟨D₀, hD₀, _⟩ := exists_finset_pole_bound (K := K)
    (Finset.univ : Finset Unit) (fun _ : Unit => q)
  refine ⟨D₁ + D₁ + D₀, ?_⟩
  intro v n
  cases n with
  | zero =>
    simp only [Finsupp.add_apply, Nat.zero_add, Nat.mul_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hq0]
    have hle : D₀ v ≤ D₁ v + D₁ v + D₀ v := by omega
    exact (neg_le_neg (Int.ofNat_le.mpr hle)).trans
      (hD₀ v () (Finset.mem_univ ()))
  | succ n =>
    have hb := hD₁ v n
    rw [map_sub, PowerSeries.coeff_C_of_ne_zero (Nat.succ_ne_zero n), sub_zero] at hb
    have hle : D₁ v * (2 * n + 1) ≤
        (D₁ v + D₁ v + D₀ v) * (n + 1 + 1) := by
      nlinarith
    simp only [Finsupp.add_apply]
    exact (neg_le_neg (Int.ofNat_le.mpr hle)).trans hb

/-- Finitely many coordinates of the same actual formal translation have
a common effective divisor, independent of the coefficient index. -/
theorem exists_formalTranslation_family_divisor_bound
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    {ι : Type*} [Finite ι] (q : ι → F) :
    ∃ D : Modulus K F, ∀ (i : ι) (v : Place K F) (n : ℕ),
      -((D v * (n + 1) : ℕ) : ℤ) ≤ v.ord (PowerSeries.coeff n (σ (q i))) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose E hE using fun i => exists_formalTranslation_divisor_bound
    (K := K) t ht σ hσt hσ0 (q i)
  refine ⟨∑ i, E i, ?_⟩
  intro i v n
  have hle : E i v ≤ (∑ j, E j) v := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (E j v)) (Finset.mem_univ i)
  exact (neg_le_neg (Int.ofNat_le.mpr (Nat.mul_le_mul_right (n + 1) hle))).trans
    (hE i v n)

omit [HasPrincipalDivisors K F] in
/-- A curve field over a perfect field supplies an actual separating
parameter, its formal translation, and one effective divisor controlling
all coefficients of a finite family of functions. -/
theorem IsCurveOver.exists_separating_formalTranslation_divisor_bound
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    {ι : Type*} [Finite ι] (q : ι → F) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K {t}) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K {t}) F ∧
      ∃ (σ : F →ₐ[K] PowerSeries F) (D : Modulus K F),
        σ t = PowerSeries.C t + PowerSeries.X ∧
        PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F ∧
        ∀ (i : ι) (v : Place K F) (n : ℕ),
          -((D v * (n + 1) : ℕ) : ℤ) ≤
            v.ord (PowerSeries.coeff n (σ (q i))) := by
  obtain ⟨t, ht, hfinite, hseparable, σ, hσ, _⟩ :=
    IsCurveOver.exists_separating_formalTranslation (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K {t}) F := hfinite
  have : Algebra.IsSeparable (IntermediateField.adjoin K {t}) F := hseparable
  obtain ⟨D, hD⟩ := exists_formalTranslation_family_divisor_bound
    t ht σ hσ.1 hσ.2 q
  exact ⟨t, ht, hfinite, hseparable, σ, D, hσ.1, hσ.2, hD⟩

end AlgebraicCurve
