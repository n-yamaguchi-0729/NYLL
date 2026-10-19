/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Nyll.SchemeTheory.RingTheory.Henselian.HenselianUnitRoots

/-!
# Roots of units over a Henselian local ring

If the residue field is separably closed and the exponent is a unit in that
field, every unit of a Henselian local ring has a root of that exponent.  This
is the characteristic-zero-compatible unit-absorption step for tame Kummer
presentations.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- A unit over a Henselian local ring has an `n`-th root when the residue
field is separably closed and `n` is invertible there. -/
theorem exists_pow_eq_of_isUnit_of_isSepClosed_residue
    {R : Type u} [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {n : ℕ} (hn : IsUnit (n : IsLocalRing.ResidueField R))
    (u : R) (hu : IsUnit u) :
    ∃ z : R, z ^ n = u := by
  let : HenselianLocalRing R :=
    { toIsLocalRing := inferInstance
      is_henselian := fun f hf a₀ hroot hder =>
        HenselianRing.is_henselian f hf a₀ hroot
          (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))) }
  have hnR : IsUnit (n : R) := by
    apply IsUnit.of_map (IsLocalRing.residue R)
    simpa only [map_natCast] using hn
  obtain ⟨w, hw⟩ := hu
  obtain ⟨z, hz⟩ :=
    HenselianLocalRing.units_pow_surjective_of_isSepClosed R n hnR w
  refine ⟨(z : R), ?_⟩
  have hval := congrArg Units.val hz
  exact (map_pow (Units.coeHom R) z n).symm.trans (hval.trans hw)

end EtaleFundamentalGroups.Kummer
