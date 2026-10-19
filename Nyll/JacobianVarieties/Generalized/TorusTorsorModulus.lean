/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.TorusRationalMapModulus
import Nyll.JacobianVarieties.Generalized.GeometricModulusUniversalProperty

/-! # Torus-torsor maps and their unpointed Abel factors

The original full divisor is a geometric modulus for any map into a torsor
under a torus. The resulting unique group/map pair needs neither a rational
curve point nor an origin of the target torsor.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsTorus G]
  (Q : Over (Spec (CommRingCat.of K))) [ModObj G.X Q]
  [IsIso (ModObj.leftSMul G.X Q)]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)

/-- Every torus-torsor map has the original full geometric modulus, in
every choice of coordinates over each algebraically closed extension. -/
theorem geometricTorsorMapHasModulus_of_isTorus :
    geometricTorsorMapHasModulus c D G Q q := by
  intro L fieldL algebraL closedL F cL DL extendedGroup action torsor algL ML qL p
  have : IsSplitTorus extendedGroup := IsTorus.geometric_split L (specMap K L)
  obtain ⟨n, ⟨e⟩⟩ := IsSplitTorus.exists_split (G := extendedGroup)
  let q₀ := (commGroupPointEquiv extendedGroup
    ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      (qL ≫ SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p)
  apply (ML.regularMapHasModulus_comp_iff_of_injective DL extendedGroup
    (GroupSchemes.splitTorus L n) q₀ e.hom
      (fun _ _ h => (cancel_mono e.hom.hom.hom.hom).mp h)).mp
  exact ML.splitTorus_regularMapHasModulus DL n _

/-- The unique equivariant Abel factor for a torus-torsor map, with no
basepoint or separate modulus hypothesis supplied by the caller. -/
theorem existsUnique_picardOneMap_torus :
    ∃! fg : (groupScheme c D ⟶ G) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  exact existsUnique_picardOneMapFromGeometricModulus_unpointed c D G Q q
    (geometricTorsorMapHasModulus_of_isTorus c D G Q q)

end AlgebraicGeometry.GeneralizedJacobian
