/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Geometric
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientGroupScheme
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric irreducibility of the scalar quotient

The class of one supplies a section of the actual projective norm open.
It therefore meets every fibre of projective space. Its geometric fibres
are nonempty open subsets of irreducible projective spaces.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped TensorProduct

namespace SchemeTheory.Affine.ProjectiveUnitOpen

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The projective class of the algebra's unit is a section over the base. -/
def unitSection : Spec (CommRingCat.of R) ⟶ carrier b :=
  Spec.map (CommRingCat.ofHom
    (ScalarQuotientPresheaf.projectivePointAlgHom b (1 : (R ⊗[R] A)ˣ)).toRingHom)

@[reassoc] theorem unitSection_toBase : unitSection b ≫ toBase b = 𝟙 _ := by
  rw [toBase_eq]
  unfold unitSection
  rw [← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (ScalarQuotientPresheaf.projectivePointAlgHom b
    (1 : (R ⊗[R] A)ˣ)).commutes r

/-- The norm open meets every fibre, even for nonreduced coefficient algebras. -/
theorem surjective_toBase : Surjective (toBase b) := by
  have : Surjective (unitSection b ≫ toBase b) := by
    rw [unitSection_toBase]
    infer_instance
  exact Surjective.of_comp (unitSection b) (toBase b)

/-- The actual projective norm open is geometrically irreducible. -/
theorem geometricallyIrreducible_toBase : GeometricallyIrreducible (toBase b) := by
  have : GeometricallyIrreducible (ProjSpace.π R n) :=
    ProjSpace.geometricallyIrreducible_π R n
  have : Surjective (projectiveι b ≫ ProjSpace.π R n) := surjective_toBase b
  change GeometricallyIrreducible (projectiveι b ≫ ProjSpace.π R n)
  infer_instance

/-- In particular, all geometric fibres of the scalar quotient are connected. -/
theorem geometricallyConnected_toBase : GeometricallyConnected (toBase b) := by
  constructor
  intro K _ y Z fst snd h
  have : IrreducibleSpace Z :=
    (geometricallyIrreducible_toBase b).geometrically_irreducibleSpace y fst snd h
  infer_instance

end SchemeTheory.Affine.ProjectiveUnitOpen

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The represented scalar quotient group scheme is geometrically connected. -/
theorem geometricallyConnected_scalarQuotientCommGroupScheme :
    GeometricallyConnected (scalarQuotientCommGroupScheme b).X.hom := by
  rw [scalarQuotientCommGroupScheme_toBase]
  exact ProjectiveUnitOpen.geometricallyConnected_toBase b

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
