/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.WholeCurveGeometricModulus

/-! # Whole-curve maps to torsors over separated commutative groups

After each algebraically closed extension, every choice of target origin turns
an everywhere-defined torsor map into an everywhere-defined group map. Its
actual full modulus then constructs the unpointed equivariant Abel factor over
the original field. No rational origin over that field is assumed.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (Q : Over (Spec (CommRingCat.of K))) [ModObj G.X Q]
  [IsIso (ModObj.leftSMul G.X Q)]
  (q : Over.mk c ⟶ Q)

/-- An everywhere-defined torsor map satisfies the full geometric modulus
condition for every effective divisor, without a rational target origin. -/
theorem geometricTorsorMapHasModulus_restriction_of_separated_group :
    geometricTorsorMapHasModulus c D G Q
      ((Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ q) := by
  intro L fieldL algebraL closedL F cL DL G_L action torsor algL ML qL p
  have : IsSeparated G_L.X.hom := by
    change IsSeparated (Limits.pullback.snd G.X.hom (specMap K L))
    infer_instance
  let U_L := modulusComplement (modulusCurveMap (c := cL) DL)
  let jL : Over.mk (U_L.ι ≫ cL) ⟶ Over.mk cL := Over.homMk U_L.ι rfl
  let r : Over.mk cL ⟶ G_L.X :=
    F.map q ≫ SchemeTheory.PointedTorsor.coordinate (G := G_L.X) p
  have he := modulusMapScalarExtension_wholeCurveRestriction c D Q q L
  change qL = jL ≫ F.map q at he
  have hcoord : qL ≫ SchemeTheory.PointedTorsor.coordinate (G := G_L.X) p = jL ≫ r := by
    rw [he, Category.assoc]
  let qr : SchemeHomOver (U_L.ι ≫ ML.toBase) G_L.X.hom :=
    ⟨U_L.ι ≫ r.left, by rw [Category.assoc, Over.w r]; rfl⟩
  have hqr :
      (commGroupPointEquiv G_L (U_L.ι ≫ cL)).symm
        (qL ≫ SchemeTheory.PointedTorsor.coordinate (G := G_L.X) p) = qr := by
    apply Subtype.ext
    exact congrArg Over.Hom.left hcoord
  exact (congrArg (ML.regularMapHasModulus DL G_L) hqr).mpr
    (ML.regularMapHasModulus_restriction_of_separated_group DL G_L r)

/-- Every whole-curve map into a torsor has its unique equivariant Picard-one
factor over the original field, in every modulus degree. -/
theorem existsUnique_picardOneMap_wholeCurve_torsor :
    let r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q :=
      (Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ q
    ∃! fg : (groupScheme c D ⟶ G) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = r ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  intro r
  exact existsUnique_picardOneMapFromGeometricModulus_unpointed c D G Q r
    (geometricTorsorMapHasModulus_restriction_of_separated_group c D G Q q)

end AlgebraicGeometry.GeneralizedJacobian
