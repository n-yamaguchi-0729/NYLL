/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.ReesChartFractions
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The chart of a regular principal ideal

The actual coefficient map to the chart at its regular generator is a ring
isomorphism. This is the affine calculation for invariance of a blowup along
an effective Cartier divisor (Stacks Project, Section 31.33).
-/

noncomputable section

universe u

namespace ReesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- If the original denominator is regular, the coefficient map is injective. -/
theorem coefficientToChart_injective (a : I) (ha : IsRegular a.val) :
    Function.Injective (coefficientToChart I a) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro r hr
  have h := congrArg
    (HomogeneousLocalization.val (𝒜 := homogeneousPart I)
      (x := Submonoid.powers (degreeOne I a))) hr
  rw [val_coefficientToChart, HomogeneousLocalization.val_zero] at h
  change algebraMap (reesAlgebra I) (Localization.Away (degreeOne I a))
    (algebraMap R (reesAlgebra I) r) = 0 at h
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (degreeOne I a)) (Localization.Away (degreeOne I a)) _).mp h
  rcases s with ⟨s, n, rfl⟩
  have hp := congrArg (fun p : reesAlgebra I => p.val.coeff n) hs
  change ((Polynomial.monomial 1 a.val) ^ n * Polynomial.C r).coeff n = 0 at hp
  rw [Polynomial.monomial_pow, one_mul, Polynomial.monomial_mul_C,
    Polynomial.coeff_monomial_same] at hp
  apply (IsRegular.pow n ha).left
  simpa only [mul_zero] using hp

/-- Every actual fraction is a coefficient when the ideal has the chart
parameter as a generator. Regularity here is supplied by the chart itself. -/
theorem coefficientToChart_surjective_of_span (a : I)
    (hI : I = Ideal.span {a.val}) : Function.Surjective (coefficientToChart I a) := by
  intro x
  obtain ⟨n, b, rfl⟩ := exists_chartFraction I a x
  have hb : b.val ∈ Ideal.span {a.val ^ n} := by
    rw [← Ideal.span_singleton_pow, ← hI]
    exact b.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨r, ?_⟩
  have ha : IsRegular (coefficientToChart I a a.val) :=
    isRegular_iff_mem_nonZeroDivisors.mpr (coefficientToChart_mem_nonZeroDivisors I a)
  apply (IsRegular.pow n ha).left
  change coefficientToChart I a a.val ^ n * coefficientToChart I a r =
    coefficientToChart I a a.val ^ n * chartFraction I a n b
  rw [coefficient_pow_mul_chartFraction]
  calc
    coefficientToChart I a a.val ^ n * coefficientToChart I a r =
        coefficientToChart I a (a.val ^ n) * coefficientToChart I a r :=
      congrArg (fun z : Chart I a => z * coefficientToChart I a r)
        (map_pow (coefficientToChart I a) a.val n).symm
    _ = coefficientToChart I a (a.val ^ n * r) :=
      (map_mul (coefficientToChart I a) (a.val ^ n) r).symm
    _ = coefficientToChart I a b.val := congrArg (coefficientToChart I a) hr.symm

/-- The coefficient ring is the actual chart of a regular principal ideal. -/
def principalChartEquiv (a : I) (hI : I = Ideal.span {a.val}) (ha : IsRegular a.val) :
    R ≃+* Chart I a :=
  RingEquiv.ofBijective (coefficientToChart I a)
    ⟨coefficientToChart_injective I a ha, coefficientToChart_surjective_of_span I a hI⟩

end ReesAlgebra
