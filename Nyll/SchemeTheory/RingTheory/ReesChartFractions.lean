/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.ReesChartRegular

/-!
# Fractions in the actual Rees charts

Every chart element is a homogeneous fraction with numerator in an actual
power of the ideal. Multiplication by the coefficient denominator clears
that fraction. These calculations include zero divisors in the base ring.
-/

noncomputable section

universe u

namespace ReesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual homogeneous fraction `b / a^n` for `b ∈ I^n`. -/
def chartFraction (a : I) (n : ℕ) (b : ↥(I ^ n)) : Chart I a :=
  HomogeneousLocalization.Away.mk (homogeneousPart I) (degreeOne_mem I a) n
    (monomial I n b) (by
      simpa only [smul_eq_mul, mul_one] using
        (show monomial I n b ∈ homogeneousPart I n from ⟨b, rfl⟩))

/-- The native homogeneous-localization presentation has numerator in an
actual ideal power. -/
theorem exists_chartFraction (a : I) (x : Chart I a) :
    ∃ (n : ℕ) (b : ↥(I ^ n)), chartFraction I a n b = x := by
  obtain ⟨n, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousPart I) (degreeOne_mem I a) x
  have hq' : q ∈ homogeneousPart I n := by
    simpa only [smul_eq_mul, mul_one] using hq
  obtain ⟨b, hb⟩ := hq'
  subst q
  exact ⟨n, b, rfl⟩

/-- Clearing the denominator recovers the actual coefficient numerator. -/
lemma val_chartFraction (a : I) (n : ℕ) (b : ↥(I ^ n)) :
    (chartFraction I a n b).val =
      Localization.mk (monomial I n b)
        (⟨degreeOne I a ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (degreeOne I a)) := rfl

/-- Clearing the denominator recovers the actual coefficient numerator. -/
theorem coefficient_pow_mul_chartFraction (a : I) (n : ℕ) (b : ↥(I ^ n)) :
    coefficientToChart I a a.val ^ n * chartFraction I a n b =
      coefficientToChart I a b.val := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (degreeOne I a))
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    val_coefficientToChart, val_chartFraction, val_coefficientToChart]
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [one_pow, OneMemClass.coe_one, one_mul]
  apply Subtype.ext
  change Polynomial.C a.val ^ n * Polynomial.monomial n b.val =
    Polynomial.monomial 1 a.val ^ n * Polynomial.C b.val
  rw [← Polynomial.C_pow, Polynomial.monomial_pow, one_mul,
    Polynomial.C_mul_monomial, Polynomial.monomial_mul_C, mul_comm (a.val ^ n)]

/-- A chart map into a ring is determined by its coefficient map whenever
the actual denominator stays regular. This is the uniqueness calculation
used by the blowup universal property. -/
theorem chartHom_ext {S : Type u} [CommRing S]
    (a : I) (φ ψ : Chart I a →+* S)
    (hcoeff : φ.comp (coefficientToChart I a) = ψ.comp (coefficientToChart I a))
    (ha : IsRegular (φ (coefficientToChart I a a.val))) : φ = ψ := by
  apply RingHom.ext
  intro x
  obtain ⟨n, b, rfl⟩ := exists_chartFraction I a x
  apply (IsRegular.pow n ha).left
  have hc (r : R) : φ (coefficientToChart I a r) = ψ (coefficientToChart I a r) :=
    congrArg (fun f : R →+* S => f r) hcoeff
  calc
    φ (coefficientToChart I a a.val) ^ n * φ (chartFraction I a n b) =
        φ (coefficientToChart I a b.val) := by
      rw [← map_pow, ← map_mul, coefficient_pow_mul_chartFraction]
    _ = ψ (coefficientToChart I a b.val) := hc b.val
    _ = φ (coefficientToChart I a a.val) ^ n * ψ (chartFraction I a n b) := by
      rw [hc a.val, ← map_pow, ← map_mul, coefficient_pow_mul_chartFraction]

end ReesAlgebra
