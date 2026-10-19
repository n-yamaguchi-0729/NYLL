/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusMapRestriction
import Nyll.JacobianVarieties.Generalized.GeometricModulusTorsorRegularMap
import Nyll.JacobianVarieties.Generalized.ModulusEmptyRegularMap
import Nyll.JacobianVarieties.Generalized.ModulusComplementFiniteExtension
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardOneAbelEquivariantUniqueness
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Degree-zero geometric modulus over an arbitrary field

A rational point defines an actual degree-one enlargement. A finite separable
extension supplies a point in its complement. Over that extension, the positive
geometric modulus constructs the group factor, and the degree-one comparison
and density extend its Abel identity to the original degree-zero modulus.
The resulting equivariant pair is suitable for finite-separable descent.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]

/-- A pointed degree-one enlargement constructs the translated group factor
for the geometric degree-zero modulus. The factor on the enlargement is
obtained from its full geometric modulus, rather than assumed. -/
theorem existsUnique_geometricGroupHom_zeroModulus_of_degreeOne
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X)
    (hmod : geometricRegularMapHasModulus c D H q)
    (E : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))))
    (hED : E.I ≤ D.I)
    (εE : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c)) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
    ∃! φ : groupScheme c D ⟶ H,
      modulusAbelMap c D ε ≫ φ.hom.hom.hom = q / (b ≫ ε ≫ q) := by
  intro b
  let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hED)
    (modulusIdealInclusion_curve c E D hED)
  have hmodE : geometricRegularMapHasModulus c E H (r ≫ q) :=
    geometricRegularMapHasModulus_restrict c D E hED H q hmod
  let φE := geometricGroupHomFromModulus c E ⟨εE.left, Over.w εE⟩ H
    ⟨(r ≫ q).left, Over.w (r ≫ q)⟩ hmodE Nat.zero_lt_one
  have hφE := geometricGroupHomFromModulus_abel_translation_over c E H εE
    (r ≫ q) hmodE Nat.zero_lt_one
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  let _ : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve c
  have : GeometricallyIntegral M.toBase := by
    change GeometricallyIntegral c
    infer_instance
  have h := M.existsUnique_groupHom_zeroModulus_of_degreeOneFactor D ε H
    ⟨q.left, Over.w q⟩ E hED εE φE hφE
  exact h

variable (Q : Over (Spec (CommRingCat.of K))) [ModObj H.X Q]
  [IsIso (ModObj.leftSMul H.X Q)]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)

include ε in
/-- The actual degree-one construction gives the unique regular equivariant
factor for a degree-zero torsor map once the enlargement has a complement point. -/
theorem existsUnique_picardOneMap_zeroModulus_of_degreeOne
    (hmod : geometricTorsorMapHasModulus c D H Q q)
    (E : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))))
    (hED : E.I ≤ D.I)
    (εE : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c)) :
    ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  let q₀ := q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε ≫ q)
  have hcoord : geometricRegularMapHasModulus c D H q₀ :=
    (geometricTorsorMapHasModulus_iff_coordinate c D H Q q (ε ≫ q)).mp hmod
  have hε : ε ≫ q₀ = 1 := by
    change ε ≫ (q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε ≫ q)) = 1
    rw [← Category.assoc]
    simpa only [toUnit_unit, Category.id_comp] using
      SchemeTheory.PointedTorsor.coordinate_basepoint (G := H.X) (ε ≫ q)
        (𝟙_ (Over (Spec (CommRingCat.of K))))
  obtain ⟨φ, hφ, _⟩ := existsUnique_geometricGroupHom_zeroModulus_of_degreeOne
    c D ε H q₀ hcoord E hED εE
  rw [hε, MonObj.comp_one, div_one] at hφ
  exact picardOneEquivariantMap_factors_uniquely c D ε q φ hφ

include ε in
/-- A rational point of the original curve supplies an actual degree-one
enlargement; a finite separable extension supplies a point outside it. The
degree-zero geometric modulus then constructs an equivariant Abel factor
over that extension, with no second ground-field point assumed. -/
theorem exists_finiteSeparableExtension_picardOneMap_zero
    (hmod : geometricTorsorMapHasModulus c D H Q q)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    ∃ L : IntermediateField K Ω, Module.Finite K L ∧ Algebra.IsSeparable K L ∧
      let cL := baseChange K c L
      let DL := D.changeBaseOfIdentity (specMap K L)
      let F := Over.pullback (specMap K L)
      let HL := (GroupSchemes.baseChange (specMap K L)).obj H
      let _ : ModObj HL.X (F.obj Q) := F.modObjObj H.X Q
      let _ : IsIso (ModObj.leftSMul HL.X (F.obj Q)) := F.isIso_leftSMul_modObjObj H.X Q
      ∃! fg : (groupScheme cL DL ⟶ HL) × (picardOne cL DL ⟶ F.obj Q),
        abelOneMap cL DL ≫ fg.2 = modulusMapScalarExtension c D L Q q ∧
          ∀ (T : Over (Spec (CommRingCat.of L)))
            (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
            (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  let E : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))) :=
    RelEffCartierDiv.ofPoint c
      (ε.left ≫ (modulusComplement (modulusCurveMap D)).ι)
      ((Category.assoc _ _ _).trans (Over.w ε))
  obtain ⟨L, hfinite, hsep, ⟨εEL⟩⟩ :=
    modulusComplement_finiteSeparableExtension_point c E Ω
  refine ⟨L, hfinite, hsep, ?_⟩
  intro cL DL F HL actionL torsorL
  let EL := E.changeBaseOfIdentity (specMap K L)
  have hEDL : EL.I ≤ DL.I := by
    rw [DL.I_eq_top_of_degree_zero]
    exact le_top
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  exact existsUnique_picardOneMap_zeroModulus_of_degreeOne cL DL
    (modulusBasepointScalarExtension c D L ε) HL (F.obj Q)
    (modulusMapScalarExtension c D L Q q)
    (geometricTorsorMapHasModulus_scalarExtension c D H Q q hmod L) EL hEDL εEL

end AlgebraicGeometry.GeneralizedJacobian
