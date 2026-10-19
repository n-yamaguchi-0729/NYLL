/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.ReesChart
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Tactic.Ring

/-!
# Regularity of the exceptional generator on a Rees chart

Although an original ideal element may be a zero divisor, its image in the
homogeneous chart at `aT` is a non-zero-divisor. Together with the explicit
principal-ideal calculation, this is the local effective Cartier calculation
for a blowup (Stacks Project, Section 31.33).
-/

noncomputable section

universe u

namespace ReesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

private theorem coefficient_regular_away (a : I) :
    algebraMap (reesAlgebra I) (Localization.Away (degreeOne I a))
      (algebraMap R (reesAlgebra I) a.val) ∈
        nonZeroDivisors (Localization.Away (degreeOne I a)) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro z hz
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (degreeOne I a)) z
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul] at hz
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (degreeOne I a))
    (S := Localization.Away (degreeOne I a)) _ _).mp hz
  rcases c with ⟨c, k, rfl⟩
  have hp := congrArg (fun p : reesAlgebra I => p.val) hc
  change (degreeOne I a).val ^ k * (Polynomial.C a.val * b.val) = 0 at hp
  apply (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (degreeOne I a))
    (S := Localization.Away (degreeOne I a)) b s).mpr
  refine ⟨⟨degreeOne I a ^ (k + 1), ⟨k + 1, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change (degreeOne I a).val ^ (k + 1) * b.val = 0
  have ha : (degreeOne I a).val = Polynomial.C a.val * Polynomial.X :=
    (Polynomial.C_mul_X_eq_monomial (a := a.val)).symm
  calc
    (degreeOne I a).val ^ (k + 1) * b.val =
        Polynomial.X * ((degreeOne I a).val ^ k * (Polynomial.C a.val * b.val)) := by
      rw [pow_succ, ha]
      ring
    _ = 0 := by rw [hp, mul_zero]

/-- The coefficient denominator is regular on its actual homogeneous chart,
without regularity or non-zero-divisor assumptions on the original ideal. -/
theorem coefficientToChart_mem_nonZeroDivisors (a : I) :
    coefficientToChart I a a.val ∈ nonZeroDivisors (Chart I a) := by
  let f : Chart I a →+* Localization.Away (degreeOne I a) :=
    algebraMap (Chart I a) (Localization.Away (degreeOne I a))
  have hf : Function.Injective f := by
    intro x y hxy
    apply HomogeneousLocalization.val_injective (𝒜 := homogeneousPart I)
      (Submonoid.powers (degreeOne I a))
    exact hxy
  apply mem_nonZeroDivisors_of_injective (f := f) hf
  change algebraMap (reesAlgebra I) (Localization.Away (degreeOne I a))
    (algebraMap R (reesAlgebra I) a.val) ∈
      nonZeroDivisors (Localization.Away (degreeOne I a))
  exact coefficient_regular_away I a

end ReesAlgebra
