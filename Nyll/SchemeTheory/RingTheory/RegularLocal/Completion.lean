/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.FlatLocalAscent
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Completion of a regular local ring

The maximal-adic completion is regular local: the actual completion map is
flat and local, and its closed fiber is the completion's residue field.
-/

@[expose] public section

noncomputable section

namespace AdicCompletion

open IsLocalRing

variable (R : Type*) [CommRing R] [IsRegularLocalRing R]

/-- The native maximal-adic completion of a regular local ring is regular local. -/
theorem isRegularLocalRing :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  have : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  apply RegularFlatLocalAscent.isRegularLocalRing_of_flat_of_isRegularLocalRing_quotient
    R (AdicCompletion (maximalIdeal R) R)
  rw [← AdicCompletion.maximalIdeal_eq_map]
  let : Field (AdicCompletion (maximalIdeal R) R ⧸
      maximalIdeal (AdicCompletion (maximalIdeal R) R)) := Ideal.Quotient.field _
  infer_instance

end AdicCompletion
