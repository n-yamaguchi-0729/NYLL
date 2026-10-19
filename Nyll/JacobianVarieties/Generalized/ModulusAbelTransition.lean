/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardOneTransitionFunctoriality
import Nyll.JacobianVarieties.Generalized.PicardOneRestrictionScheme
import Nyll.JacobianVarieties.Generalized.PicardOneEquivariantMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelRestriction
import Nyll.JacobianVarieties.Generalized.ModulusTransition
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap

/-! # The pointed Abel square for the full modulus transition

The intrinsic torsor transition is equivariant for the actual group transition.
Taking coordinates at corresponding Abel points therefore gives the pointed
Abel square over any field, without a pointwise density argument.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))

/-- The actual group transition takes the normalized Abel map to the normalized
Abel map for the smaller full modulus, at the same actual basepoint. -/
theorem modulusAbelMap_transitionAlong :
    modulusAbelMap c D ε ≫ (transitionAlong c D D' j w).hom.hom.hom =
      modulusComplementRestriction c j w ≫
        modulusAbelMap c D' (ε ≫ modulusComplementRestriction c j w) := by
  let r := modulusComplementRestriction c j w
  let p := ε ≫ abelOneMap c D
  let p' := (ε ≫ r) ≫ abelOneMap c D'
  let φ := (transitionAlong c D D' j w).hom.hom.hom
  let t := picardOneTransitionAlong c D D' j w
  have hp : p ≫ t = p' := by
    change (ε ≫ abelOneMap c D) ≫ picardOneTransitionAlong c D D' j w = _
    rw [Category.assoc, abelOneMap_transitionAlong, ← Category.assoc]
  have ht : t = SchemeTheory.PointedTorsor.map φ p p' :=
    SchemeTheory.PointedTorsor.map_unique φ p p' t hp
      (fun _ g x => picardOneTransitionAlong_smul c D D' j w g x)
  have hc : t ≫ SchemeTheory.PointedTorsor.coordinate p' =
      SchemeTheory.PointedTorsor.coordinate p ≫ φ := by
    rw [ht]
    exact SchemeTheory.PointedTorsor.map_coordinate φ p p'
  have ha : abelOneMap c D ≫ SchemeTheory.PointedTorsor.coordinate p =
      modulusAbelMap c D ε := by
    simpa only [Category.id_comp] using abelOneMap_pointCoordinate c D ε (𝟙 _)
  calc
    modulusAbelMap c D ε ≫ φ =
        (abelOneMap c D ≫ SchemeTheory.PointedTorsor.coordinate p) ≫ φ := by rw [ha]
    _ = abelOneMap c D ≫ (t ≫ SchemeTheory.PointedTorsor.coordinate p') := by
      rw [Category.assoc, hc]
    _ = (r ≫ abelOneMap c D') ≫ SchemeTheory.PointedTorsor.coordinate p' := by
      rw [← Category.assoc]
      exact congrArg (fun f => f ≫ SchemeTheory.PointedTorsor.coordinate p')
        (abelOneMap_transitionAlong c D D' j w)
    _ = r ≫ modulusAbelMap c D' (ε ≫ r) :=
      abelOneMap_pointCoordinate c D' (ε ≫ r) r

end AlgebraicGeometry.GeneralizedJacobian
