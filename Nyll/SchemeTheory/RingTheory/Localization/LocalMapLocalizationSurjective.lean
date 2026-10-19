/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Surjectivity of a local map into a localization

If the image of a local map already contains the numerator ring of a
localization, localness also puts the inverses of its denominators in the
image. This is shared by the geometric-stalk double and triple overlaps.
-/

namespace IsLocalization

/-- A local coefficient map containing all numerators contains the whole
localization. The range premise concerns the given numerator map; no
surjectivity of the coefficient map is assumed. -/
theorem surjective_algebraMap_of_numerators_mem_range
    {T B L : Type*} [CommRing T] [CommRing B] [CommRing L]
    [Algebra T B] [Algebra B L] [Algebra T L] [IsScalarTower T B L]
    [IsLocalHom (algebraMap T L)] (M : Submonoid B) [IsLocalization M L]
    (hrange : ∀ b : B, ∃ t : T, algebraMap T L t = algebraMap B L b) :
    Function.Surjective (algebraMap T L) := by
  intro x
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨t, ht⟩ := hrange b
  obtain ⟨d, hd⟩ := hrange s
  have hdunit : IsUnit d := IsLocalHom.map_nonunit d
    (hd.symm ▸ IsLocalization.map_units L s)
  obtain ⟨dunit, hdunit⟩ := hdunit
  refine ⟨t * ↑(dunit⁻¹), ?_⟩
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [← hd, ← hdunit, ← map_mul, mul_assoc, Units.inv_mul, mul_one, ht]

end IsLocalization
