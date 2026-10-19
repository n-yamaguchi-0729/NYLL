/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Generalized.GroupProjectionConnected
import Nyll.JacobianVarieties.Generalized.GroupProjectionGeometry
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralSmooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Geometric integrality of the generalized Jacobian and its forgetting fibres

These statements hold over the original field and for every effective modulus.
The fibre statement includes fibres over non-rational points of the ordinary Jacobian.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The constructed generalized Jacobian is geometrically integral over its ground field. -/
instance groupScheme_geometricallyIntegral : GeometricallyIntegral (groupScheme c D).X.hom := by
  have h := geometry c D
  have : SmoothOfRelativeDimension (geometricGenus K c + (d - 1))
      (groupScheme c D).X.hom := h.1
  have : Smooth (groupScheme c D).X.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + (d - 1)) (groupScheme c D).X.hom
  have : GeometricallyConnected (groupScheme c D).X.hom := h.2.2.2.2
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected _

/-- The same scheme is integral before extending the ground field. -/
instance groupScheme_isIntegral : IsIntegral (groupScheme c D).X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton (groupScheme c D).X.hom

/-- Forgetting the rigidification has geometrically integral fibres over every point. -/
theorem groupProjection_geometricallyIntegral :
    GeometricallyIntegral (groupProjection c D).hom.hom.hom.left := by
  have : Smooth (groupProjection c D).hom.hom.hom.left := groupProjection_smooth c D
  have : GeometricallyConnected (groupProjection c D).hom.hom.hom.left :=
    groupProjection_geometricallyConnected c D
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected _

end AlgebraicGeometry.GeneralizedJacobian
