/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeUnitRestriction
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionFibers

/-! # Geometry of unit restriction for actual finite closed subschemes -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct

namespace SchemeTheory.Affine.FiniteScheme

variable {K : Type u} [Field K] {D D' : Scheme.{u}}
  (q : D ⟶ Spec (CommRingCat.of K)) (q' : D' ⟶ Spec (CommRingCat.of K))
  (j : D' ⟶ D) (w : j ≫ q = q')

/-- Restriction of actual global sections with their original coefficient actions. -/
def coordinateRestriction : coordinateAlgebra q →ₐ[K] coordinateAlgebra q' :=
  ((algΓ (CommRingCat.of K)).map (Over.homMk j w)).unop.hom

/-- The coordinate-algebra restriction is literally pullback of global sections. -/
theorem coordinateRestriction_toRingHom :
    (coordinateRestriction q q' j w).toRingHom = j.appTop.hom := rfl

variable [IsFinite q] [IsClosedImmersion j]

/-- The closed inclusion supplies surjectivity of the actual coordinate homomorphism. -/
theorem coordinateRestriction_surjective :
    Function.Surjective (coordinateRestriction q q' j w) := by
  have : IsAffine D := isAffine_of_isAffineHom q
  change Function.Surjective j.appTop.hom
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine j).2

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bD : Basis ι K (coordinateAlgebra q)) (bD' : Basis κ K (coordinateAlgebra q'))

omit [IsFinite q] [IsClosedImmersion j] in
/-- The norm-open map obtained from restriction on the actual finite schemes. -/
def unitRestrictionNormMap : UnitNormPolynomial.unitOpen bD ⟶ UnitNormPolynomial.unitOpen bD' :=
  UnitNormPolynomial.restrictionMap bD bD' (coordinateRestriction q q' j w)

omit [IsFinite q] [IsClosedImmersion j] in
/-- Its action on every algebra-valued point is actual restriction of tensor units. -/
theorem unitRestrictionNormMap_point {L : Type u} [CommRing L] [Algebra K L]
    (g : UnitNormPolynomial.CoordinateRing bD →ₐ[K] L) :
    UnitNormPolynomial.homEquivUnits bD'
        (g.comp (UnitNormPolynomial.restrictionRingHom bD bD'
          (coordinateRestriction q q' j w))) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id K L)
        (coordinateRestriction q q' j w)).toRingHom.toMonoidHom
          (UnitNormPolynomial.homEquivUnits bD g) :=
  UnitNormPolynomial.restrictionRingHom_homEquiv bD bD' (coordinateRestriction q q' j w) g

/-- Restriction of units of actual finite closed subschemes is smooth. -/
theorem smooth_unitRestrictionNormMap : Smooth (unitRestrictionNormMap q q' j w bD bD') :=
  UnitNormPolynomial.smooth_restrictionMap bD' (coordinateRestriction q q' j w)
    (coordinateRestriction_surjective q q' j w) bD

/-- Every point of the target unit norm open lifts. -/
theorem surjective_unitRestrictionNormMap :
    Surjective (unitRestrictionNormMap q q' j w bD bD') :=
  UnitNormPolynomial.surjective_restrictionMap bD bD' (coordinateRestriction q q' j w)
    (coordinateRestriction_surjective q q' j w)

/-- Its geometric fibres are nonempty irreducible opens of affine spaces. -/
theorem geometricallyIrreducible_unitRestrictionNormMap :
    GeometricallyIrreducible (unitRestrictionNormMap q q' j w bD bD') :=
  UnitNormPolynomial.geometricallyIrreducible_restrictionMap bD bD'
    (coordinateRestriction q q' j w) (coordinateRestriction_surjective q q' j w)

/-- In particular, actual finite-scheme unit restriction has geometrically connected fibres. -/
theorem geometricallyConnected_unitRestrictionNormMap :
    GeometricallyConnected (unitRestrictionNormMap q q' j w bD bD') :=
  UnitNormPolynomial.geometricallyConnected_restrictionMap bD bD'
    (coordinateRestriction q q' j w) (coordinateRestriction_surjective q q' j w)

end SchemeTheory.Affine.FiniteScheme
