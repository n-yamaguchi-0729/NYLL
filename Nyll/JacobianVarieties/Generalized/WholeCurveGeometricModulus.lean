/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.WholeCurveGroupModulus
import Nyll.JacobianVarieties.Generalized.ProperTargetModulus
import Nyll.JacobianVarieties.Generalized.GeometricModulusPointedUniversalProperty
import Nyll.JacobianVarieties.Generalized.GeometricModulusUniversalProperty

/-! # Whole-curve maps to separated groups over arbitrary fields

The zero-modulus theorem is applied after each algebraically closed extension.
Restriction commutes with the actual curve and target pullbacks, so the result
uses the same original divisor and gives an Abel factor over the original field.
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
  (q : Over.mk c ⟶ G.X)

/-- A map defined on the whole curve satisfies the geometric modulus
condition for every full effective divisor, for any separated group target. -/
theorem geometricRegularMapHasModulus_restriction_of_separated_group :
    geometricRegularMapHasModulus c D G
      ((Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ q) := by
  intro L fieldL algebraL closedL cL DL algL ML qL
  let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
  have : IsSeparated G_L.X.hom := by
    change IsSeparated (Limits.pullback.snd G.X.hom (specMap K L))
    infer_instance
  let r : Over.mk cL ⟶ G_L.X := (Over.pullback (specMap K L)).map q
  have he := modulusMapScalarExtension_wholeCurveRestriction c D G.X q L
  change qL = _ at he
  let qr : SchemeHomOver
      ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase) G_L.X.hom :=
    ⟨(modulusComplement (modulusCurveMap DL)).ι ≫ r.left,
      by rw [Category.assoc, Over.w r]; rfl⟩
  have hqr : (⟨qL.left, Over.w qL⟩ : SchemeHomOver
      ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase) G_L.X.hom) = qr := by
    apply Subtype.ext
    exact congrArg Over.Hom.left he
  exact (congrArg (ML.regularMapHasModulus DL G_L) hqr).mpr
    (ML.regularMapHasModulus_restriction_of_separated_group DL G_L r)

/-- A whole-curve map has a unique translated generalized-Jacobian factor
over its original field, without a modulus or proper-target hypothesis. -/
theorem existsUnique_groupHom_wholeCurve_geometric_translation
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    let r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X :=
      (Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ q
    ∃! φ : groupScheme c D ⟶ G,
      modulusAbelMap c D ε ≫ φ.hom.hom.hom =
        r / (toUnit (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) ≫ ε ≫ r) := by
  intro r
  exact existsUnique_groupHom_geometricModulus_translation c D ε G r
    (geometricRegularMapHasModulus_restriction_of_separated_group c D G q)

/-- The unpointed Abel factor of a whole-curve group-valued map, with no
rational curve point or target properness assumption. -/
theorem existsUnique_picardOneMap_wholeCurve_group :
    let r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X :=
      (Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ q
    ∃! fg : (groupScheme c D ⟶ G) × (picardOne c D ⟶ G.X),
      abelOneMap c D ≫ fg.2 = r ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) * (x ≫ fg.2) := by
  intro r
  let _ : ModObj G.X G.X := ModObj.regular G.X
  have : IsIso (ModObj.leftSMul G.X G.X) :=
    SchemeTheory.PointedTorsor.isIso_leftSMul_regular G.X
  have ht : geometricTorsorMapHasModulus c D G G.X r := by
    apply (geometricTorsorMapHasModulus_iff_coordinate c D G G.X r η[G.X]).mpr
    simpa only [SchemeTheory.PointedTorsor.coordinate_regular_unit, Category.comp_id] using
      geometricRegularMapHasModulus_restriction_of_separated_group c D G q
  exact existsUnique_picardOneMapFromGeometricModulus_unpointed c D G G.X r ht

end AlgebraicGeometry.GeneralizedJacobian
