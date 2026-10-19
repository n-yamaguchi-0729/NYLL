/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.GenericPoint
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-! Projective space is geometrically irreducible over every coefficient ring. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every field-valued base change of projective space is the corresponding
projective space over that field, and hence is irreducible. -/
theorem geometricallyIrreducible_π (R : Type u) [CommRing R] (n : ℕ) :
    GeometricallyIrreducible (π R n) := by
  constructor
  intro K _ y Z fst snd h
  let : Algebra R K := (Spec.preimage y).hom.toAlgebra
  have hp := isPullback_map R K n
  have hy : Spec.map (CommRingCat.ofHom (algebraMap R K)) = y :=
    Spec.map_preimage y
  rw [hy] at hp
  have : IrreducibleSpace (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) :=
    irreducibleSpace K n
  exact (h.isoIsPullback _ _ hp).hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

end AlgebraicGeometry.ProjSpace
