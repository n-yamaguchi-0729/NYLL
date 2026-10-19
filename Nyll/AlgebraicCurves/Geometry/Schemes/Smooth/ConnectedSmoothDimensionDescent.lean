/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothRelativeDimension
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothSmoothOfRelativeDimension
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Descent of the dimension of a connected smooth scheme

After smoothness and connectedness have descended, the constant smooth dimension
is determined on any nonempty scalar extension. Comparing actual smooth charts
proves the equality without an additional dimension hypothesis over the base.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry

private theorem smoothRelativeDimension_eq_of_point
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (x : X) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by
  obtain ⟨U, hU, hxU, hn⟩ :=
    SmoothRelativeDimensionConstancy.exists_isStandardSmoothOfRelativeDimension_appLE_top f n x
  obtain ⟨V, hV, hxV, hm⟩ :=
    SmoothRelativeDimensionConstancy.exists_isStandardSmoothOfRelativeDimension_appLE_top f m x
  exact SmoothRelativeDimensionConstancy.relativeDimension_eq_of_mem_inter hU hV hn hm hxU hxV

/-- The dimension measured on a nonempty field extension is the dimension of the
same smooth geometrically connected scheme over the original field. -/
theorem smoothOfRelativeDimension_of_connected_scalarExtension
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] [GeometricallyConnected f]
    {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of L)) (x₀ : X')
    (n : ℕ) [SmoothOfRelativeDimension n x']
    (e : pullback f (specMap K L) ≅ X')
    (he : e.hom ≫ x' = baseChange K f L) :
    SmoothOfRelativeDimension n f := by
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton f
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace f
  have : SmoothOfRelativeDimension m f := hm
  have hbc : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension m) :=
    smoothOfRelativeDimension_isStableUnderBaseChange m
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension m) := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro g h j
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk j.inv.w))
  have : SmoothOfRelativeDimension m (baseChange K f L) :=
    hbc.of_isPullback (IsPullback.of_hasPullback f (specMap K L)) hm
  have hi : e.inv ≫ baseChange K f L = x' := by
    rw [← he, Iso.inv_hom_id_assoc]
  have : SmoothOfRelativeDimension m x' := by
    rw [← hi]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@SmoothOfRelativeDimension m) e.inv (baseChange K f L)).mpr inferInstance
  exact (smoothRelativeDimension_eq_of_point x' x₀ m n) ▸ hm

end AlgebraicGeometry
