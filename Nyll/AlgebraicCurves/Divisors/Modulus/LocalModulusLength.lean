/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The degree of a local modulus quotient

For a discrete valuation ring over a field, the quotient by the `n`-th power
of its maximal ideal has dimension `n` times the residue-field degree. The
finite-dimensionality of the quotient follows from its length and the finite
residue degree; it is not an additional hypothesis.
-/

noncomputable section

namespace IsDiscreteValuationRing

variable (K R : Type*) [Field K] [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Algebra K R]
  [IsLocalHom (algebraMap K R)] [Module.Finite K (IsLocalRing.ResidueField R)]

/-- The local quotient contributing a multiplicity `n` to a divisor has
dimension `n` times its residue degree over the ground field. -/
theorem finrank_quotient_pow_maximalIdeal (n : ℕ) :
    Module.finrank K (R ⧸ IsLocalRing.maximalIdeal R ^ n) =
      n * Module.finrank K (IsLocalRing.ResidueField R) := by
  have hresidue :
      Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField R) =
        (Module.finrank K (IsLocalRing.ResidueField R) : ℕ∞) := by
    rw [← Module.length_eq_of_surjective
      (R := IsLocalRing.ResidueField K) (S := K)
      (M := IsLocalRing.ResidueField R) (IsLocalRing.residue_surjective (R := K)),
      Module.length_eq_finrank]
  have hlength : Module.length K (R ⧸ IsLocalRing.maximalIdeal R ^ n) =
      ((n * Module.finrank K (IsLocalRing.ResidueField R) : ℕ) : ℕ∞) := by
    rw [IsLocalRing.length_restrictScalars K R
      (R ⧸ IsLocalRing.maximalIdeal R ^ n), length_quotient_pow_maximalIdeal,
      hresidue, Nat.cast_mul]
  have hfiniteLength : IsFiniteLength K (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
    apply Module.length_ne_top_iff.mp
    rw [hlength]
    exact ENat.natCast_ne_top _
  have : IsNoetherian K (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
  have : Module.Finite K (R ⧸ IsLocalRing.maximalIdeal R ^ n) := inferInstance
  have hnat := congrArg ENat.toNat hlength
  simpa only [Module.length_eq_finrank, ENat.toNat_natCast] using hnat

end IsDiscreteValuationRing
