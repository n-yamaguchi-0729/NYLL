/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Localization.ArtinianUnitLifting
import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual restriction of units to a closed subscheme of a finite field-scheme -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open SchemeTheory.Affine.FiniteScheme

namespace SchemeTheory

variable {K : Type u} [Field K] {D D' : Scheme.{u}}
  (q : D ⟶ Spec (CommRingCat.of K)) [IsFinite q]
  (j : D' ⟶ D) [IsClosedImmersion j]

include q

/-- Units of the actual global sections restrict surjectively to every closed subscheme
of a finite scheme over a field. Nonreduced and disconnected moduli are included. -/
theorem finiteScheme_unitsRestriction_surjective :
    Function.Surjective (Units.map j.appTop.hom.toMonoidHom) := by
  have : IsAffine D := isAffine_of_isAffineHom q
  have hArtinian : IsArtinianRing (coordinateAlgebra q) := isArtinian_of_tower K inferInstance
  have : IsArtinianRing Γ(D, ⊤) := hArtinian
  exact artinian_unitsMap_surjective j.appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine j).2

end SchemeTheory
