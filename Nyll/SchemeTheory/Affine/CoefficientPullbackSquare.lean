/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The cartesian square of an actual coefficient pullback map

The two projection formulas for a coefficient change identify its square
as a pullback. This retains the existing coefficient map and the original
algebra structures when applying base-change results to it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchemeTheory.Affine.FiniteScheme

universe u

/-- The existing coefficient-change morphism is the actual base change
of the morphism of coefficient spectra. -/
theorem coefficientPullbackMap_isPullback
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (g : A →ₐ[k] B) :
    IsPullback (coefficientPullbackMap f g)
      (pullback.snd f (coefficientMap (K := k) B))
      (pullback.snd f (coefficientMap (K := k) A))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
  apply IsPullback.of_right (p := coefficientPullbackMap_snd f g)
    (t := IsPullback.of_hasPullback f (coefficientMap (K := k) A))
  rw [coefficientPullbackMap_fst, coefficientMap_naturality]
  exact IsPullback.of_hasPullback f (coefficientMap (K := k) B)

end SchemeTheory.Affine.FiniteScheme
