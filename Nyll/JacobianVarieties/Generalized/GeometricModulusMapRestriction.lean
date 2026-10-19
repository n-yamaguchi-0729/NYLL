/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusRegularMap
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusAbelTransition
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric
import Nyll.JacobianVarieties.Generalized.ModulusTransition
import Nyll.JacobianVarieties.Generalized.ModulusMapRestriction
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.DivisorRestrictionScalarExtension
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBaseSubscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Enlarging a geometric modulus over the original field

The actual group factor for the smaller positive modulus and the actual
modulus transition give the restricted factor. Its Abel identity supplies
the geometric principal-divisor condition, retaining all multiplicities.
-/

noncomputable section

universe u

open CategoryTheory NeronModelInfra
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d e : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (E : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of K))))
  (hED : E.I ≤ D.I)
  (εE : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
  (hmod : geometricRegularMapHasModulus c D G q)
  (hd : 0 < d)

private theorem geometricRestriction_factor_translation :
    let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve c E D hED)
    let εD : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
      ⟨(εE ≫ r).left, Over.w (εE ≫ r)⟩
    let φD := geometricGroupHomFromModulus c D εD G ⟨q.left, Over.w q⟩ hmod hd
    let bE : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
    modulusAbelMap c E εE ≫ (transition c E D hED ≫ φD).hom.hom.hom =
      (r ≫ q) / (bE ≫ εE ≫ r ≫ q) := by
  intro r εD φD bE
  let bD : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
  have hb : r ≫ bD = bE := by
    apply Over.OverMorphism.ext
    exact Over.w r
  have hAbel := modulusAbelMap_transitionAlong c E D
    (Scheme.IdealSheafData.inclusion hED)
    (modulusIdealInclusion_curve c E D hED) εE
  change modulusAbelMap c E εE ≫ (transition c E D hED).hom.hom.hom =
    r ≫ modulusAbelMap c D (εE ≫ r) at hAbel
  have hD := geometricGroupHomFromModulus_abel_translation c D εD G
    ⟨q.left, Over.w q⟩ hmod hd
  change modulusAbelMap c D (εE ≫ r) ≫ φD.hom.hom.hom =
    q / (bD ≫ (εE ≫ r) ≫ q) at hD
  change modulusAbelMap c E εE ≫
    ((transition c E D hED).hom.hom.hom ≫ φD.hom.hom.hom) = _
  rw [← Category.assoc, hAbel, Category.assoc, hD, GrpObj.comp_div]
  rw [← Category.assoc r bD, hb, Category.assoc]

include hmod in
omit [IsSeparated G.X.hom] in
/-- Enlarging the full geometric modulus preserves its principal-divisor
condition in every degree, without a rational complement point. The ideal
inclusion and actual complement restriction are transported together. -/
theorem geometricRegularMapHasModulus_restrict :
    let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve c E D hED)
    geometricRegularMapHasModulus c E G (r ≫ q) := by
  intro r L fieldL algebraL closedL cL EL algL ML qEL
  let DL := D.changeBaseOfIdentity (SmoothProperCurve.specMap K L)
  let G_L := (GroupSchemes.baseChange (SmoothProperCurve.specMap K L)).obj G
  let qDL := modulusGroupMapScalarExtension c D L G q
  have hEDL : EL.I ≤ DL.I := by
    change (E.I.comap _).comap _ ≤ (D.I.comap _).comap _
    exact Scheme.IdealSheafData.comap_mono _
      (Scheme.IdealSheafData.comap_mono _ hED)
  let rL := modulusComplementRestriction cL (Scheme.IdealSheafData.inclusion hEDL)
    (modulusIdealInclusion_curve cL EL DL hEDL)
  let rL' := modulusComplementRestriction cL
    (divisorRestrictionScalarMap E D (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve c E D hED) L)
    (divisorRestrictionScalarMap_square E D (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve c E D hED) L)
  have hrL : rL' = rL := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (modulusComplement (modulusCurveMap DL)).ι).mp
    dsimp only [rL', rL, modulusComplementRestriction, Over.homMk_left]
  have hq : qEL = rL ≫ qDL := by
    have h := modulusMapScalarExtension_restriction c E L D
      (Scheme.IdealSheafData.inclusion hED) (modulusIdealInclusion_curve c E D hED) G.X q
    change qEL = rL' ≫ qDL at h
    exact h.trans (congrArg (fun t => t ≫ qDL) hrL)
  have hD : ML.regularMapHasModulus DL G_L ⟨qDL.left, Over.w qDL⟩ := hmod L
  have hE := ML.regularMapHasModulus_restrict DL EL hEDL G_L
    ⟨qDL.left, Over.w qDL⟩ hD
  change ML.regularMapHasModulus EL G_L
    ((GoodReductionJacobian.commGroupPointEquiv G_L
      ((modulusComplement (modulusCurveMap EL)).ι ≫ cL)).symm qEL)
  rw [hq]
  exact hE

/-- The constructed positive-degree factors commute with the full modulus
transition over arbitrary ground fields. -/
theorem geometricGroupHomFromModulus_restrict (he : 0 < e) :
    let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve c E D hED)
    let εD : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
      ⟨(εE ≫ r).left, Over.w (εE ≫ r)⟩
    let qE : SchemeHomOver ((modulusComplement (modulusCurveMap E)).ι ≫ c) G.X.hom :=
      ⟨(r ≫ q).left, Over.w (r ≫ q)⟩
    let hmodE := geometricRegularMapHasModulus_restrict c D E hED G q hmod
    geometricGroupHomFromModulus c E ⟨εE.left, Over.w εE⟩ G qE hmodE he =
      transition c E D hED ≫
        geometricGroupHomFromModulus c D εD G ⟨q.left, Over.w q⟩ hmod hd := by
  intro r εD qE hmodE
  apply modulusAbel_groupHom_ext c E εE G
  exact (geometricGroupHomFromModulus_abel_translation c E
    ⟨εE.left, Over.w εE⟩ G qE hmodE he).trans
      (geometricRestriction_factor_translation c D E hED εE G q hmod hd).symm

end AlgebraicGeometry.GeneralizedJacobian
