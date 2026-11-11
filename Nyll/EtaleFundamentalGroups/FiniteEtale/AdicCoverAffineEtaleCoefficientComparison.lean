/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineAlgebra
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineProjective
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Agreement of the actual affine quotient coefficient maps

The algebra map defined by quotient descent and the map obtained from the
actual closed-level section ring agree on every original coefficient.
Surjectivity of the quotient projection identifies the two maps on their
whole domain. Thus their algebraic properties can be used with the single
native coefficient action in the completed cover algebra.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- Quotient descent of the original coefficient action is the actual
coefficient map through the closed-level section-ring comparison. -/
theorem affineSectionQuotientAlgebraMap_toRingHom (U : X.affineOpens) (n : ℕ) :
    (affineSectionQuotientAlgebraMap f I V U n).toRingHom =
      affineSectionCoefficient f I V U n := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ((affineSectionQuotientAlgebraMap f I V U n).commutes a).trans
    (affineSectionCoefficient_mk f I V U n a).symm

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
