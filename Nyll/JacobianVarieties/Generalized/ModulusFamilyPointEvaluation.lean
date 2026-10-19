/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusPointEvaluation
import Nyll.JacobianVarieties.Generalized.ModulusAbelCanonicalPoint
import Nyll.JacobianVarieties.Generalized.ModulusPointClassification
import Nyll.JacobianVarieties.Generalized.PicardZeroChartDifference
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.JacobianVarieties.Generalized.CorrectedDivisorSumField
import Nyll.JacobianVarieties.Albanese.OpenCurveSumChoice
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedInOfPoint
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.JacobianVarieties.Generalized.ModulusClosedFieldPoints

/-! # The regular family sum and the actual additive point evaluation -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian JacobianVarieties.Albanese
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)

/-- A genuine regular family sum evaluates its actual corrected generalized Jacobian point. -/
theorem modulusFamilySum_eq_modulusPointEvaluation
    (hmod : M.regularMapHasModulus D G q) {n : ℕ}
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K))))
    (hE : E.SupportedIn (modulusComplement (modulusCurveMap D))) :
    let U := modulusComplement (modulusCurveMap D)
    let P := RelEffCartierDiv.ofPoint M.toBase (ε.1 ≫ U.ι)
      ((Category.assoc _ _ _).trans ε.2)
    let hP := RelEffCartierDiv.supportedIn_ofPoint (f := M.toBase)
      (ε.1 ≫ U.ι) ((Category.assoc _ _ _).trans ε.2) U (fun x => (ε.1 x).property)
    ∀ hz : modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
        modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n ∈
      modulusPicardZeroSubgroup M.toBase (modulusCurveMap D)
        (Over.mk (𝟙 (Spec (CommRingCat.of K)))),
      commGroupPointValue G (𝟙 _)
          (modulusFamilySum M.toBase D ε (commGroupRelativeLaw G)
            (commGroupRelativeLaw_isCommutative G) q E hE) =
        M.modulusPointEvaluation D (M.regularMapValues U G q) hmod
          (Additive.ofMul (rigidifiedZeroClassPointEquiv M.toBase D
            ⟨modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
              modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n, hz⟩)) := by
  intro U P hP hz
  let a := M.regularMapValues U G q
  let v := commGroupPointValue G (𝟙 (Spec (CommRingCat.of K)))
  let S := chooseOpenCurveSum M.toBase U (commGroupRelativeLaw G) q n
    (commGroupRelativeLaw_isCommutative G) ε
  have hsum := M.value_correctedSupportedDivisorSum_field U S.universal S.tupleMap
    S.tupleMap_toBase S.tuple_ideal (commGroupRelativeLaw G) q S.sum S.tuple_sum
    (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q)
    v (commGroupPointValue_one G (𝟙 _)) (commGroupPointValue_mul G (𝟙 _))
    a (M.regularMapValues_apply U G q) E hE
  have hpoint := M.modulusPointEvaluation_correctedFamily D
    ⟨ε.1 ≫ U.ι, (Category.assoc _ _ _).trans ε.2⟩ a hmod E hE P hP n hz
  have hbase : Divisor.evaluation a
      (M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor =
      v (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q) :=
    (M.divisorEvaluation_ofPoint a
      ⟨ε.1 ≫ U.ι, (Category.assoc _ _ _).trans ε.2⟩).trans
        (M.regularMapValues_apply U G q ε)
  rw [hbase] at hpoint
  exact hsum.trans hpoint.symm

/-- Pulling an actual chart sum to a rational point gives the additive evaluation
of the same point, using the atlas's constructed divisor representative. -/
theorem modulusFamilySum_pullback_eq_modulusPointEvaluation
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d)
    (j : (generalizedJacobianDivisorAtlas M.toBase D ε hd).cover.I₀)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((generalizedJacobianDivisorAtlas M.toBase D ε hd).cover.f j ≫
        (groupScheme M.toBase D).X.hom)) :
    commGroupPointValue G (𝟙 _)
        (modulusFamilySum M.toBase D ε (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q
          (((generalizedJacobianDivisorAtlas M.toBase D ε hd).divisor j).pullbackAlong
            z.left (Over.w z))
          (((generalizedJacobianDivisorAtlas M.toBase D ε hd).supported j).pullbackAlong
            z.left (Over.w z))) =
      M.modulusPointEvaluation D
        (M.regularMapValues (modulusComplement (modulusCurveMap D)) G q) hmod
        (Additive.ofMul (z ≫
          (Over.homMk ((generalizedJacobianDivisorAtlas M.toBase D ε hd).cover.f j) :
            Over.mk ((generalizedJacobianDivisorAtlas M.toBase D ε hd).cover.f j ≫
              (groupScheme M.toBase D).X.hom) ⟶ (groupScheme M.toBase D).X))) := by
  let atlas := generalizedJacobianDivisorAtlas M.toBase D ε hd
  let U := modulusComplement (modulusCurveMap D)
  let P := RelEffCartierDiv.ofPoint M.toBase (ε.1 ≫ U.ι)
    ((Category.assoc _ _ _).trans ε.2)
  have hP : P.SupportedIn U := RelEffCartierDiv.supportedIn_ofPoint
    (f := M.toBase) (ε.1 ≫ U.ι) ((Category.assoc _ _ _).trans ε.2) U
    (fun x => (ε.1 x).property)
  let E : RelEffCartierDiv M.toBase (atlas.degree j)
      (𝟙 (Spec (CommRingCat.of K))) :=
    (atlas.divisor j).pullbackAlong z.left (Over.w z)
  have hE : E.SupportedIn U := (atlas.supported j).pullbackAlong z.left (Over.w z)
  let raw := (modulusPicardZeroPresheaf M.toBase (modulusCurveMap D)).map z.op
    (atlas.rawClass j)
  have hclass : modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
      modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ atlas.degree j =
      raw.val := by
    have h := atlas.familyClass_div_point_pow_pullback_eq_rawClass
      (t := 𝟙 (Spec (CommRingCat.of K))) j z.left (Over.w z)
    have he : GoodReductionJacobian.schemeHomOverComp
        (𝟙 (Spec (CommRingCat.of K))) (Category.comp_id _) ε = ε := by
      apply Subtype.ext
      exact Category.id_comp ε.1
    rw [he] at h
    exact h
  have hz : modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
      modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ atlas.degree j ∈
      modulusPicardZeroSubgroup M.toBase (modulusCurveMap D)
        (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [hclass]
    exact raw.property
  have hpoint :
      rigidifiedZeroClassPointEquiv M.toBase D
          ⟨modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
            modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ atlas.degree j,
            hz⟩ =
        z ≫ (Over.homMk (atlas.cover.f j) :
          Over.mk (atlas.cover.f j ≫ (groupScheme M.toBase D).X.hom) ⟶
            (groupScheme M.toBase D).X) :=
    (congrArg (rigidifiedZeroClassPointEquiv M.toBase D)
      (Subtype.ext hclass)).trans
        (generalizedJacobianDivisorAtlas_rawClass_point M.toBase D ε hd j z)
  have hsum := M.modulusFamilySum_eq_modulusPointEvaluation D ε G q hmod E hE hz
  rw [hpoint] at hsum
  exact hsum

/-- Equality of the full corrected frames determines the actual regular
family sum, without a separate zero-class membership hypothesis. -/
theorem modulusFamilySum_eq_of_correctedClass
    (hmod : M.regularMapHasModulus D G q) {n₀ n₁ : ℕ}
    (E₀ : RelEffCartierDiv M.toBase n₀ (𝟙 (Spec (CommRingCat.of K))))
    (hE₀ : E₀.SupportedIn (modulusComplement (modulusCurveMap D)))
    (E₁ : RelEffCartierDiv M.toBase n₁ (𝟙 (Spec (CommRingCat.of K))))
    (hE₁ : E₁.SupportedIn (modulusComplement (modulusCurveMap D))) :
    let b : RigidifiedLineBundle.Classes
        (modulusBaseChange M.toBase (modulusCurveMap D) (𝟙 (Spec (CommRingCat.of K)))) :=
      modulusAbelPointClass M.toBase (modulusCurveMap D)
        (T := Over.mk (𝟙 (Spec (CommRingCat.of K)))) (Over.homMk ε.1 ε.2)
    modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E₀ hE₀ / b ^ n₀ =
        modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E₁ hE₁ / b ^ n₁ →
      modulusFamilySum M.toBase D ε (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q E₀ hE₀ =
        modulusFamilySum M.toBase D ε (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q E₁ hE₁ := by
  intro b hclass
  let U := modulusComplement (modulusCurveMap D)
  let P := RelEffCartierDiv.ofPoint M.toBase (ε.1 ≫ U.ι)
    ((Category.assoc _ _ _).trans ε.2)
  have hP : P.SupportedIn U := RelEffCartierDiv.supportedIn_ofPoint
    (f := M.toBase) (ε.1 ≫ U.ι) ((Category.assoc _ _ _).trans ε.2) U
    (fun z => (ε.1 z).property)
  have hPclass : modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP = b :=
    (modulusAbelPointClass_eq_canonical M.toBase (modulusCurveMap D)
      (T := Over.mk (𝟙 (Spec (CommRingCat.of K)))) (Over.homMk ε.1 ε.2)).symm
  rw [← hPclass] at hclass
  let a := M.regularMapValues U G q
  let v := commGroupPointValue G (𝟙 (Spec (CommRingCat.of K)))
  have heval := M.divisorEvaluation_sub_nsmul_eq_of_familyClass_div_pow_eq D a hmod
    E₀ hE₀ E₁ hE₁ P hP n₀ n₁ hclass
  have hbase : Divisor.evaluation a
      (M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor =
        v (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q) :=
    (M.divisorEvaluation_ofPoint a
      ⟨ε.1 ≫ U.ι, (Category.assoc _ _ _).trans ε.2⟩).trans
      (M.regularMapValues_apply U G q ε)
  rw [hbase] at heval
  let S₀ := chooseOpenCurveSum M.toBase U (commGroupRelativeLaw G) q n₀
    (commGroupRelativeLaw_isCommutative G) ε
  let S₁ := chooseOpenCurveSum M.toBase U (commGroupRelativeLaw G) q n₁
    (commGroupRelativeLaw_isCommutative G) ε
  apply commGroupPointValue_injective G (𝟙 (Spec (CommRingCat.of K)))
  change v (correctedSupportedDivisorSum M.toBase U S₀.universal (commGroupRelativeLaw G)
      S₀.sum (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q) E₀ hE₀) =
    v (correctedSupportedDivisorSum M.toBase U S₁.universal (commGroupRelativeLaw G)
      S₁.sum (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q) E₁ hE₁)
  rw [M.value_correctedSupportedDivisorSum_field U S₀.universal S₀.tupleMap
    S₀.tupleMap_toBase S₀.tuple_ideal (commGroupRelativeLaw G) q S₀.sum S₀.tuple_sum
    (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q)
    v (commGroupPointValue_one G (𝟙 _)) (commGroupPointValue_mul G (𝟙 _))
    a (M.regularMapValues_apply U G q),
    M.value_correctedSupportedDivisorSum_field U S₁.universal S₁.tupleMap
      S₁.tupleMap_toBase S₁.tuple_ideal (commGroupRelativeLaw G) q S₁.sum S₁.tuple_sum
      (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q)
      v (commGroupPointValue_one G (𝟙 _)) (commGroupPointValue_mul G (𝟙 _))
      a (M.regularMapValues_apply U G q)]
  exact heval

end AlgebraicCurve.CurveModel
