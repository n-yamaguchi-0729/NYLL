/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMap
import Nyll.SchemeTheory.Affine.FiniteSchemeUnitRestriction
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Restriction of actual whole-modulus units on field-valued tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (j : D' ⟶ D) (w : i' = j ≫ i) [IsClosedImmersion j]

/-- The actual morphism used to restrict rigidifications remains a closed immersion
on every test scheme. -/
theorem modulusRestrictionPullback_isClosedImmersion {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    IsClosedImmersion (modulusRestrictionPullback c j w t) :=
  MorphismProperty.pullbackLift_fst_snd (P := @IsClosedImmersion) t
    (by rw [w, Category.assoc]) inferInstance

variable [IsFinite (i ≫ c)]

/-- Over every field-valued parameter, every unit on the smaller whole modulus
lifts to an actual unit on the larger modulus. -/
theorem modulusRestrictionUnits_surjective {L : Type u} [Field L]
    (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) :
    Function.Surjective
      (Units.map (modulusRestrictionPullback c j w t).appTop.hom.toMonoidHom) := by
  have : IsClosedImmersion (modulusRestrictionPullback c j w t) :=
    modulusRestrictionPullback_isClosedImmersion c j w t
  exact SchemeTheory.finiteScheme_unitsRestriction_surjective
    (pullback.snd (i ≫ c) t) (modulusRestrictionPullback c j w t)

end AlgebraicGeometry.GeneralizedJacobian
