/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.EventuallyNormalizedSection
import Nyll.JacobianVarieties.Generalized.NormalizedSectionNonzero
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Concrete divisor representatives of rigidified line bundles

On a geometric curve with nonempty Cartier modulus, every chosen rigidified
line bundle is a quotient of canonically rigidified effective divisors away
from the full modulus. The numerator is the zero divisor of the normalized
section constructed by twisting at a rational point outside the modulus.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

private theorem fiberPointIdeal_isInvertible
    {C S : Scheme.{u}} {c : C ⟶ S} [IsProper c]
    [SmoothOfRelativeDimension 1 c]
    {K : Type u} [Field K] (x : Spec (CommRingCat.of K) ⟶ S)
    (ε : Spec (CommRingCat.of K) ⟶ Limits.pullback c x)
    (hε : ε ≫ Limits.pullback.snd c x = 𝟙 _) : ε.ker.IsInvertible := by
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (Limits.pullback.snd c x) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback c x) inferInstance
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε

/-- Every actual rigidified class has an effective numerator and a point-power
denominator, both disjoint from the whole modulus. -/
theorem exists_divisor_quotient_representative
    {C S : Scheme.{u}} {c : C ⟶ S} [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ S)
    (𝒱 : (Limits.pullback c x).TwoAffineOpenCover)
    (I : (Limits.pullback c x).IdealSheafData) (hI : I.IsInvertible) [Nonempty I.subscheme]
    (ε : Spec (CommRingCat.of K) ⟶ Limits.pullback c x)
    (hε : ε ≫ Limits.pullback.snd c x = 𝟙 _)
    (havoid : ∀ y : I.subscheme, I.subschemeι.base y ∉ ε.ker.support)
    (M : RigidifiedLineBundle I.subschemeι) :
    ∃ (n r : ℕ) (E : RelEffCartierDiv c r x)
      (ha : ∀ y : I.subscheme, I.subschemeι.base y ∉ E.I.support)
      (hb : ∀ y : I.subscheme, I.subschemeι.base y ∉ (ε.ker ^ (n + 1)).support),
      classOf M =
        classOf (ofInvertibleIdeal I.subschemeι E.I (RelEffCartierDiv.isInvertible_I E) ha) /
        classOf (ofInvertibleIdeal I.subschemeι (ε.ker ^ (n + 1))
          ((fiberPointIdeal_isInvertible x ε hε).pow (n + 1)) hb) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (Limits.pullback.snd c x) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback c x) inferInstance
  have : IsIntegral (Limits.pullback c x) :=
    GeometricallyIntegral.geometrically_isIntegral x (Limits.pullback.fst c x)
      (Limits.pullback.snd c x) (IsPullback.of_hasPullback c x)
  obtain ⟨N, hN⟩ := eventually_exists_normalizedSection
    (Limits.pullback.snd c x) 𝒱 I hI ε hε havoid M
  obtain ⟨hb, s, hs⟩ := hN N le_rfl
  let P := ofInvertibleIdeal I.subschemeι (ε.ker ^ (N + 1))
    ((Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow (N + 1)) hb
  have hs0 : s ≠ 0 := normalizedSection_ne_zero (M.tensor P) s hs
  obtain ⟨r, E, ha, _hzero, ⟨e⟩⟩ :=
    exists_effectiveDivisor_of_normalizedSection x (M.tensor P) s hs0 hs
  refine ⟨N, r, E, ha, hb, ?_⟩
  apply eq_div_iff_mul_eq'.mpr
  exact (classOf_eq_iff (M.tensor P)
    (ofInvertibleIdeal I.subschemeι E.I (RelEffCartierDiv.isInvertible_I E) ha)).mpr ⟨e⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
