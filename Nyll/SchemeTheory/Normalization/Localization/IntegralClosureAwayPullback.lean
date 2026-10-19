/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral

/-!
# The actual away pullback of a normalization in an algebra

Integral closure commutes with restricting the base to an away open.
The ambient algebra is an arbitrary commutative ring, so this comparison
applies to the entire generic tensor algebra of a cover, including all
components created by a field extension.

The map between the two integral closures is the original inclusion in
the ambient algebra. The resulting spectrum square is a pullback with
the original coefficient and localization maps. This identifies the
restriction of a normalized root cover before comparing it to the
original cover on the boundary complement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchemeTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (f : R) [Algebra (Localization.Away f) A]
  [IsScalarTower R (Localization.Away f) A]

/-- The actual inclusion of integral closures when the coefficient ring
is localized away from one element. -/
def integralClosureAwayRingHom :
    integralClosure R A →+* integralClosure (Localization.Away f) A where
  toFun x := ⟨x.val, x.property.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The normalization after restricting the base to the away open is the
actual pullback of the original normalization, for a whole ambient algebra. -/
theorem isPullback_spec_integralClosure_away :
    IsPullback
      (Spec.map (CommRingCat.ofHom (integralClosureAwayRingHom R A f)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.Away f) (integralClosure (Localization.Away f) A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  let S := Localization.Away f
  let C := integralClosure R A
  let E := integralClosure S A
  let i : C →+* E := integralClosureAwayRingHom R A f
  let : Algebra C E := i.toAlgebra
  have : IsScalarTower R C E := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    apply Subtype.ext
    rfl
  have : IsScalarTower C E A := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rfl
  have hf : IsUnit (algebraMap R A f) := by
    rw [IsScalarTower.algebraMap_apply R S A]
    exact (IsLocalization.Away.algebraMap_isUnit f).map (algebraMap S A)
  have : IsLocalization.Away (algebraMap R A f) A :=
    IsLocalization.away_of_isUnit_of_bijective A hf Function.bijective_id
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers f)) A := by
    change IsLocalization ((Submonoid.powers f).map (algebraMap R A)) A
    rw [Submonoid.map_powers]
    infer_instance
  have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers f)) E :=
    IsLocalization.integralClosure (S := A) (Rf := S) (Sf := A) (Submonoid.powers f)
  have : Algebra.IsPushout R C S E :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers f) S C E
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R C S E)

end SchemeTheory
