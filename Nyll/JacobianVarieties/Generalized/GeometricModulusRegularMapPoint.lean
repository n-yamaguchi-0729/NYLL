/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionClasses
import Nyll.JacobianVarieties.Generalized.PicardZeroChartDifference
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ReducedSmoothOverField
import Nyll.JacobianVarieties.Generalized.GeometricModulusAtlasGluing
import Nyll.JacobianVarieties.Generalized.ModulusPointClassification
import Nyll.JacobianVarieties.Generalized.ModulusFamilyPointEvaluation
import Nyll.JacobianVarieties.Generalized.ModulusAbelGroupScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusAbelCanonicalPoint
import Nyll.JacobianVarieties.Generalized.ModulusFamilySumScalarExtension

/-! # Geometric point values of the regular map over the ground field

A point lifts to the original divisor atlas. The actual framed class of that
divisor and its corrected regular sum both transport to the extended curve.
Their existing point classification identifies the result with the additive
full-modulus evaluation over the closed extension field.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ c) G.X.hom)
  (hmod : geometricRegularMapHasModulus c D G (Over.homMk q.1 q.2))

/-- The actual regular map has the full divisor evaluation on every geometric point. -/
theorem geometricModulusRegularMap_point (hd : 0 < d)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (p : (Over.map (specMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
      (groupScheme c D).X) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
    let qL := modulusGroupMapScalarExtension c D L G (Over.homMk q.1 q.2)
    let _ : Algebra L (pullback c (specMap K L)).functionField :=
      (AlgebraicCurve.baseToFunctionField cL).toAlgebra
    let ML := AlgebraicCurve.CurveModel.ofSmoothProperCurve cL
    let _ : GeometricallyIntegral ML.toBase := by
      change GeometricallyIntegral cL
      infer_instance
    let hmodL : ML.regularMapHasModulus DL G_L ⟨qL.left, Over.w qL⟩ := hmod L
    let f := geometricModulusRegularMap c D ε G q hmod hd
    Additive.ofMul ((Over.mapPullbackAdj (specMap K L)).homEquiv
      (Over.mk (𝟙 (Spec (CommRingCat.of L)))) G.X (p ≫ Over.homMk f.1 f.2)) =
      ML.modulusPointEvaluation DL
        (ML.regularMapValues (modulusComplement (modulusCurveMap DL)) G_L
          ⟨qL.left, Over.w qL⟩) hmodL
        (Additive.ofMul ((groupScalarExtensionPointEquiv c D L
          (Over.mk (𝟙 (Spec (CommRingCat.of L))))).symm p)) := by
  intro cL DL G_L qL algL ML geometricML hmodL f
  let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let t := T.hom
  let εK : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) := Over.homMk ε.1 ε.2
  let εL := modulusBasepointScalarExtension c D L εK
  have : IsSeparated G_L.X.hom := by
    change IsSeparated (pullback.snd G.X.hom (specMap K L))
    infer_instance
  have : SmoothOfRelativeDimension (geometricGenus K c + (d - 1))
      (groupScheme c D).X.hom := (geometry c D).1
  have : Smooth (groupScheme c D).X.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + (d - 1)) _
  have : IsReduced (groupScheme c D).X.left :=
    isReduced_of_smooth_over_field (g := (groupScheme c D).X.hom) inferInstance
  let atlas := generalizedJacobianDivisorAtlas c D ε hd
  obtain ⟨j, z, hz, hs⟩ := geometricModulusAtlasSum_fieldPoint c D ε G q hmod atlas p
  let E : RelEffCartierDiv c (atlas.degree j) ((Over.map (specMap K L)).obj T).hom :=
    (atlas.divisor j).pullbackAlong z.left (Over.w z)
  let hE : E.SupportedIn (modulusComplement (modulusCurveMap D)) :=
    (atlas.supported j).pullbackAlong z.left (Over.w z)
  let EL := (RelEffCartierDiv.changeBaseEquiv c (specMap K L) t (atlas.degree j)).symm E
  let hEL := divisorScalarExtensionSupported c D L t E hE
  let raw := (modulusPicardZeroPresheaf c (modulusCurveMap D)).map z.op (atlas.rawClass j)
  let eRaw := ((modulusPicardZeroGroup_divisorScalarExtensionIso (c := c) D L).app
    (op T)).commGroupIsoToMulEquiv
  let rawL := eRaw.symm raw
  have hraw : eRaw rawL = raw := eRaw.apply_symm_apply raw
  let b : (Over.map (specMap K L)).obj T ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk (t ≫ specMap K L) (Category.comp_id _)
  let εclass : RigidifiedLineBundle.Classes
      (modulusBaseChange c (modulusCurveMap D) ((Over.map (specMap K L)).obj T).hom) :=
    modulusAbelPointClass c (modulusCurveMap D) (b ≫ εK)
  have hframe : modulusDivisorFamilyClass c (modulusCurveMap D) E hE /
      εclass ^ atlas.degree j = raw.val := by
    have h := atlas.familyClass_div_point_pow_pullback_eq_rawClass j z.left (Over.w z)
    have he := modulusAbelPointClass_eq_canonical c (modulusCurveMap D)
      (b ≫ εK)
    dsimp only [εclass]
    rw [he]
    exact h
  have hεL : divisorScalarExtensionPoint c D L εL = b ≫ εK :=
    divisorScalarExtensionPoint_lift c D L _
  let εclassL : RigidifiedLineBundle.Classes (modulusBaseChange cL (modulusCurveMap DL) t) :=
    modulusAbelPointClass cL (modulusCurveMap DL) (T := Over.mk t) εL
  have hframeL : modulusDivisorFamilyClass cL (modulusCurveMap DL) EL hEL /
      εclassL ^ atlas.degree j = rawL.val := by
    apply (divisorScalarExtensionClassesEquiv c D L t).injective
    dsimp only [εclassL]
    have hp := divisorScalarExtensionClassesEquiv_abelPoint c D L (T := Over.mk t) εL
    simp only [Over.mk_hom] at hp
    rw [map_div, map_pow, divisorScalarExtensionClassesEquiv_divisorFamily c D L t E hE,
      hp, hεL]
    exact hframe.trans (congrArg Subtype.val hraw).symm
  let UL := modulusComplement (modulusCurveMap DL)
  let PL : RelEffCartierDiv cL 1 t := RelEffCartierDiv.ofPoint cL (εL.left ≫ UL.ι)
    ((Category.assoc _ _ _).trans (Over.w εL))
  let hPL : PL.SupportedIn UL := RelEffCartierDiv.supportedIn_ofPoint (f := cL)
    (εL.left ≫ UL.ι) ((Category.assoc _ _ _).trans (Over.w εL)) UL
    (fun x => (εL.left x).property)
  have hPLclass : modulusDivisorFamilyClass cL (modulusCurveMap DL) PL hPL =
      εclassL :=
    (modulusAbelPointClass_eq_canonical cL (modulusCurveMap DL) εL).symm
  have hzL : modulusDivisorFamilyClass cL (modulusCurveMap DL) EL hEL /
      modulusDivisorFamilyClass cL (modulusCurveMap DL) PL hPL ^ atlas.degree j ∈
        modulusPicardZeroSubgroup cL (modulusCurveMap DL) T := by
    rw [hPLclass, hframeL]
    exact rawL.property
  let ePoint := groupScalarExtensionPointEquiv c D L T
  have hpoint : rigidifiedZeroClassPointEquiv cL DL rawL = ePoint.symm p := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply]
    apply (pointEquiv c D ((Over.map (specMap K L)).obj T)).injective
    rw [groupScalarExtensionPointEquiv_rigidifiedClass c D L rawL]
    change (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app
        (op ((Over.map (specMap K L)).obj T)) (eRaw rawL) = _
    rw [hraw]
    have h := generalizedJacobianDivisorAtlas_rawClass_classifies c D ε hd j z
    rw [hz] at h
    exact h
  have heval := ML.modulusFamilySum_eq_modulusPointEvaluation DL
    ⟨εL.left, Over.w εL⟩ G_L ⟨qL.left, Over.w qL⟩ hmodL EL hEL hzL
  have hrawL : (⟨modulusDivisorFamilyClass cL (modulusCurveMap DL) EL hEL /
      modulusDivisorFamilyClass cL (modulusCurveMap DL) PL hPL ^ atlas.degree j,
      hzL⟩ : modulusPicardZeroSubgroup cL (modulusCurveMap DL) T) = rawL := by
    apply Subtype.ext
    change modulusDivisorFamilyClass cL (modulusCurveMap DL) EL hEL /
      modulusDivisorFamilyClass cL (modulusCurveMap DL) PL hPL ^ atlas.degree j = rawL.val
    rw [hPLclass]
    exact hframeL
  change _ = ML.modulusPointEvaluation DL
    (ML.regularMapValues UL G_L ⟨qL.left, Over.w qL⟩) hmodL
    (Additive.ofMul (rigidifiedZeroClassPointEquiv cL DL
      (⟨modulusDivisorFamilyClass cL (modulusCurveMap DL) EL hEL /
        modulusDivisorFamilyClass cL (modulusCurveMap DL) PL hPL ^ atlas.degree j,
        hzL⟩ : modulusPicardZeroSubgroup cL (modulusCurveMap DL) T))) at heval
  rw [hrawL, hpoint] at heval
  have hsum : (Over.mapPullbackAdj (specMap K L)).homEquiv T G.X
      (p ≫ Over.homMk f.1 f.2) =
      commGroupPointEquiv G_L t
        (modulusFamilySum cL DL ⟨εL.left, Over.w εL⟩ (commGroupRelativeLaw G_L)
          (commGroupRelativeLaw_isCommutative G_L) ⟨qL.left, Over.w qL⟩ EL hEL) := by
    exact (congrArg (fun r => (Over.mapPullbackAdj (specMap K L)).homEquiv T G.X
      (commGroupPointEquiv G (t ≫ specMap K L) r)) hs).trans
        (modulusFamilySum_scalarExtension_geometric c D (Over.homMk ε.1 ε.2)
          G (Over.homMk q.1 q.2) L E hE)
  rw [hsum]
  exact heval

end AlgebraicGeometry.GeneralizedJacobian
