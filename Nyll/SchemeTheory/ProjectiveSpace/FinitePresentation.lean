/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Ring.ULift

/-!
# Finite presentation of projective space over an arbitrary ring

The existing coefficient-change square identifies projective space with
the base change of projective space over the integers. Finite type over
that Noetherian base gives finite presentation before base change.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjSpace

instance locallyOfFinitePresentation_π (R : Type u) [CommRing R] (n : ℕ) :
    LocallyOfFinitePresentation (π R n) := by
  let : Algebra (ULift.{u} ℤ) R :=
    ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  exact CategoryTheory.MorphismProperty.of_isPullback
    (isPullback_map (ULift.{u} ℤ) R n)
    (inferInstanceAs (LocallyOfFinitePresentation (π (ULift.{u} ℤ) n)))

end AlgebraicGeometry.ProjSpace
