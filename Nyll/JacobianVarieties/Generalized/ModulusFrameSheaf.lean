/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusPicardNaturality
import Nyll.JacobianVarieties.Generalized.PicardSheaf
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# The actual frame family embeds in the modulus Picard sheaf

Sheafification of the natural, pointwise injective classification gives an
embedding over the parameter scheme. The target uses the existing full modulus
Picard sheaf. Identifying the total family with its degree-zero part is separate.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) {L : (pullback c s).Modules}
  (hL : Scheme.Modules.IsInvertible L)

/-- The frame family maps to the actual modulus Picard sheaf over the same parameter base. -/
def modulusFrameSheafToPicard :
    scalarFrameSheaf (pullback.snd (modulusBaseMap D) s)
        ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L) ⟶
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) s).obj
        (modulusPicardSheaf c (modulusCurveMap D)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
      (modulusFramesToPicard D s hL) ≫
    ((Functor.pushforwardContinuousSheafificationCompatibility
      (G := Over.map s) (A := Type (u + 1))
      (J := Scheme.fppfTopology.over S)
      (K := Scheme.fppfTopology.over (Spec (CommRingCat.of K)))).app
        (modulusPicardPresheaf c (modulusCurveMap D))).hom

/-- Sheafification preserves the actual injective classification of the fixed family. -/
instance modulusFrameSheafToPicard_mono : Mono (modulusFrameSheafToPicard D s hL) := by
  have hm : Mono ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
      (modulusFramesToPicard D s hL)) := inferInstance
  let e := (Functor.pushforwardContinuousSheafificationCompatibility
    (G := Over.map s) (A := Type (u + 1))
    (J := Scheme.fppfTopology.over S)
    (K := Scheme.fppfTopology.over (Spec (CommRingCat.of K)))).app
      (modulusPicardPresheaf c (modulusCurveMap D))
  dsimp only [modulusFrameSheafToPicard]
  exact mono_comp' hm (show Mono e.hom from inferInstance)

end AlgebraicGeometry.GeneralizedJacobian
