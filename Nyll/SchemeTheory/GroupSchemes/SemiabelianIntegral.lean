/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.SemiabelianGeometry
import Nyll.SchemeTheory.Morphisms.SmoothGeometricallyIntegral
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Geometric integrality of semiabelian varieties and their quotient fibres

The torus translation description supplies geometric connectedness of the actual
quotient fibres. Smoothness makes those fibres, and the semiabelian source,
geometrically integral.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {G : CommGrp (Over (Spec (CommRingCat.of K)))}

namespace SemiabelianExtension

/-- Every fibre of the actual torus-by-abelian quotient is geometrically integral. -/
theorem projection_geometricallyIntegral (E : SemiabelianExtension G) :
    GeometricallyIntegral E.projection.hom.hom.hom.left := by
  have : Smooth E.projection.hom.hom.hom.left := E.projection_smooth
  have : GeometricallyConnected E.projection.hom.hom.hom.left :=
    E.projection_geometricallyConnected
  exact Smooth.geometricallyIntegral_of_geometricallyConnected E.projection.hom.hom.hom.left

end SemiabelianExtension

namespace IsSemiabelian

/-- A semiabelian variety is geometrically integral over its ground field. -/
instance geometricallyIntegral [IsSemiabelian G] : GeometricallyIntegral G.X.hom :=
  Smooth.geometricallyIntegral_of_geometricallyConnected G.X.hom

/-- The actual underlying scheme of a semiabelian variety is integral. -/
instance isIntegral [IsSemiabelian G] : IsIntegral G.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom

end IsSemiabelian

end AlgebraicGeometry
