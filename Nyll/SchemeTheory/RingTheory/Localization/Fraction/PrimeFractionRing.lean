/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The fraction ring of a prime localization

The fraction ring of `R_p`, with its original coefficient map from the
domain `R`, is also a fraction ring of `R`. The proof composes the two
actual localizations and identifies the resulting denominator monoid.
This allows a boundary calculation and a global normalization to use the
same chosen field, without assuming a comparison of their fraction fields.
-/

namespace SchemeTheory

universe u v

/-- A fraction ring of a prime localization is a fraction ring of the
original domain, for the compatible original coefficient maps. -/
theorem isFractionRing_of_localizationAtPrime
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [CommRing K]
    (p : Ideal R) [p.IsPrime]
    [Algebra R K] [Algebra (Localization.AtPrime p) K]
    [IsScalarTower R (Localization.AtPrime p) K]
    [IsFractionRing (Localization.AtPrime p) K] :
    IsFractionRing R K := by
  let V := Localization.AtPrime p
  have hloc : IsLocalization
      ((nonZeroDivisors V).comap (algebraMap R V)) K :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      p.primeCompl (nonZeroDivisors V) K (fun _ hx ↦ hx.mem_nonZeroDivisors)
  have hdenom : (nonZeroDivisors V).comap (algebraMap R V) = nonZeroDivisors R := by
    ext r
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero,
      map_ne_zero_iff _ (IsLocalization.injective V p.primeCompl_le_nonZeroDivisors)]
  have hresult : IsLocalization (nonZeroDivisors R) K := hdenom ▸ hloc
  exact hresult

end SchemeTheory
