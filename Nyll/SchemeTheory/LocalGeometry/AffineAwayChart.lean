/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Defs

/-!
# Actual affine charts after inverting a base element

For an algebra `R → A`, the literal map between the two away
localizations gives the cartesian spectrum square. Its algebra and
scalar-tower compatibility are proved from the actual localization map.

An affine open chart of a scheme over `R` therefore gives an actual open
chart on its base change to `R[1/r]`, with coordinate ring `A[1/r]`.
This identifies the local generic cover in the specialization construction
as the pullback of the original global generic cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchemeTheory

universe u

private theorem awayMap_algebraMap_base
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (r a : R) :
    Localization.awayMap (algebraMap R A) r
        (algebraMap R (Localization.Away r) a) =
      algebraMap A (Localization.Away (algebraMap R A r)) (algebraMap R A a) :=
  IsLocalization.map_eq _ a

/-- The original away map is the base change of the principal open
immersion, with the coefficient and localization maps unchanged. -/
theorem isPullback_spec_algebraMap_away
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (r : R) :
    let S := Localization.Away r
    let T := Localization.Away (algebraMap R A r)
    let : Algebra S T := (Localization.awayMap (algebraMap R A) r).toAlgebra
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap A T)))
      (Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  intro S T aST
  have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S T := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap R T a =
      Localization.awayMap (algebraMap R A) r (algebraMap R S a)
    exact (IsScalarTower.algebraMap_apply R A T a).trans
      (awayMap_algebraMap_base R A r a).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers r)) T := by
    change IsLocalization ((Submonoid.powers r).map (algebraMap R A)) T
    rw [Submonoid.map_powers]
    exact Localization.isLocalization
  have : Algebra.IsPushout R A S T :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers r) S A T
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R A S T)

/-- A given affine open chart restricts to the actual affine chart on the
base change that inverts a chosen element of the base ring. -/
theorem exists_affineAwaySchemeChart
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (v : Spec (.of A) ⟶ X) [IsOpenImmersion v]
    (hv : v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))) (r : R) :
    let S := Localization.Away r
    let T := Localization.Away (algebraMap R A r)
    let : Algebra S T := (Localization.awayMap (algebraMap R A) r).toAlgebra
    let s := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let j := Spec.map (CommRingCat.ofHom (algebraMap A T))
    ∃ w : Spec (.of T) ⟶ pullback f s,
      IsOpenImmersion w ∧ IsPullback j w v (pullback.fst f s) ∧
        w ≫ pullback.snd f s = Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  intro S T aST s j
  let t := Spec.map (CommRingCat.ofHom (algebraMap S T))
  have hAway : IsPullback j t
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) s :=
    isPullback_spec_algebraMap_away R A r
  have hcomm : (j ≫ v) ≫ f = t ≫ s := by
    rw [Category.assoc, hv]
    exact hAway.w
  let w : Spec (.of T) ⟶ pullback f s := pullback.lift (j ≫ v) t hcomm
  have hfst : w ≫ pullback.fst f s = j ≫ v := pullback.lift_fst _ _ _
  have hsnd : w ≫ pullback.snd f s = t := pullback.lift_snd _ _ _
  have hOuter : IsPullback j (w ≫ pullback.snd f s) (v ≫ f) s := by
    rw [hsnd, hv]
    exact hAway
  have hChart : IsPullback j w v (pullback.fst f s) :=
    hOuter.of_bot hfst.symm (IsPullback.of_hasPullback f s)
  exact ⟨w, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hChart inferInstance,
    hChart, hsnd⟩

end SchemeTheory
