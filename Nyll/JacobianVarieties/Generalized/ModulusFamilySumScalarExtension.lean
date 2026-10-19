/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Albanese.CorrectedDivisorSums
import Nyll.JacobianVarieties.Albanese.OpenCurveSumChoice
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionClasses
import Nyll.JacobianVarieties.Albanese.DivisorSumEvaluation
import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBasePointSums
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedDivisorGeometricTuples
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw

/-! # Geometric values of corrected divisor sums under scalar extension

An actual supported divisor over an algebraically closed extension is
decomposed into points, retaining every multiplicity. Its projected tuple
represents the original family. The two constructed regular sums therefore
agree under the native group-point adjunction, including the degree correction.
No modulus condition on the target map is needed for this comparison.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian JacobianVarieties.Albanese
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)

/-- The actual corrected sum of a geometric divisor commutes with the
full-divisor scalar extension and the native target-group pullback. -/
theorem modulusFamilySum_scalarExtension_geometric
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    {n : ℕ}
    (E : RelEffCartierDiv c n (𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L))
    (hE : E.SupportedIn (modulusComplement (modulusCurveMap D))) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let εL := modulusBasepointScalarExtension c D L ε
    let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
    let _ : IsSeparated extendedGroup.X.hom := by
      change IsSeparated (pullback.snd G.X.hom (specMap K L))
      infer_instance
    let qL := modulusGroupMapScalarExtension c D L G q
    let EL := (RelEffCartierDiv.changeBaseEquiv c (specMap K L) (𝟙 _) n).symm E
    let hEL := divisorScalarExtensionSupported c D L (𝟙 _) E hE
    (Over.mapPullbackAdj (specMap K L)).homEquiv
        (Over.mk (𝟙 (Spec (CommRingCat.of L)))) G.X
        (commGroupPointEquiv G (𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L)
          (modulusFamilySum c D ⟨ε.left, Over.w ε⟩ (commGroupRelativeLaw G)
            (commGroupRelativeLaw_isCommutative G) ⟨q.left, Over.w q⟩ E hE)) =
      commGroupPointEquiv extendedGroup (𝟙 (Spec (CommRingCat.of L)))
        (modulusFamilySum cL DL ⟨εL.left, Over.w εL⟩ (commGroupRelativeLaw extendedGroup)
          (commGroupRelativeLaw_isCommutative extendedGroup) ⟨qL.left, Over.w qL⟩ EL hEL) := by
  intro cL DL εL extendedGroup separatedGL qL EL hEL
  let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let U := modulusComplement (modulusCurveMap D)
  let UL := modulusComplement (modulusCurveMap DL)
  let adj := Over.mapPullbackAdj (specMap K L)
  let φ : Additive ((Over.map (specMap K L)).obj T ⟶ G.X) ≃+
      Additive (T ⟶ extendedGroup.X) := (adj.homMulEquiv T G.X).toAdditive
  let vK : SchemeHomOver (T.hom ≫ specMap K L) G.X.hom →
      Additive (T ⟶ extendedGroup.X) := fun x =>
    φ (commGroupPointValue G (T.hom ≫ specMap K L) x)
  let vL : SchemeHomOver T.hom extendedGroup.X.hom →
      Additive (T ⟶ extendedGroup.X) := commGroupPointValue extendedGroup T.hom
  have hvK₁ : vK ((commGroupRelativeLaw G).one (T.hom ≫ specMap K L)) = 0 := by
    change φ (commGroupPointValue G _ ((commGroupRelativeLaw G).one _)) = 0
    rw [commGroupPointValue_one, map_zero]
  have hvK₂ (x y : SchemeHomOver (T.hom ≫ specMap K L) G.X.hom) :
      vK ((commGroupRelativeLaw G).mul (T.hom ≫ specMap K L) x y) = vK x + vK y := by
    change φ (commGroupPointValue G (T.hom ≫ specMap K L)
      ((commGroupRelativeLaw G).mul (T.hom ≫ specMap K L) x y)) =
      φ (commGroupPointValue G (T.hom ≫ specMap K L) x) +
        φ (commGroupPointValue G (T.hom ≫ specMap K L) y)
    rw [commGroupPointValue_mul]
    exact φ.map_add _ _
  let qK : SchemeHomOver (U.ι ≫ c) G.X.hom := ⟨q.left, Over.w q⟩
  let qL' : SchemeHomOver (UL.ι ≫ cL) extendedGroup.X.hom := ⟨qL.left, Over.w qL⟩
  let S := chooseOpenCurveSum c U (commGroupRelativeLaw G) qK n
    (commGroupRelativeLaw_isCommutative G) ⟨ε.left, Over.w ε⟩
  let SL := chooseOpenCurveSum cL UL (commGroupRelativeLaw extendedGroup) qL' n
    (commGroupRelativeLaw_isCommutative extendedGroup) ⟨εL.left, Over.w εL⟩
  obtain ⟨xsL, hfullL, hopenL⟩ :=
    RelEffCartierDiv.exists_supported_geometric_tuple cL UL EL hEL
  let extendedPoints : Fin n → (T ⟶ Over.mk (UL.ι ≫ cL)) := fun i =>
    Over.homMk (xsL i).1 (xsL i).2
  let xs : Fin n → SchemeHomOver (T.hom ≫ specMap K L) (U.ι ≫ c) := fun i =>
    ⟨(divisorScalarExtensionPoint c D L (extendedPoints i)).left,
      Over.w (divisorScalarExtensionPoint c D L (extendedPoints i))⟩
  have hfull : E.I = prodKerGraph c (fun i => (xs i).1 ≫ U.ι)
      (fun i => (Category.assoc _ _ _).trans (xs i).2) := by
    let ps : Fin n → SchemeHomOver T.hom cL := fun i =>
      ⟨(xsL i).1 ≫ UL.ι, (Category.assoc _ _ _).trans (xsL i).2⟩
    have hproj := RelEffCartierDiv.changeBaseEquiv_I_eq_prodKerGraph c
      (specMap K L) T.hom EL ps hfullL
    simp only [EL, T, Over.mk_hom, Equiv.apply_symm_apply] at hproj
    apply hproj.trans
    congr 1
    funext i
    exact (divisorScalarExtensionPoint_inclusion c D L (extendedPoints i)).symm
  have hopen : (E.restrictToOpen c U hE).I =
      prodKerGraph (U.ι ≫ c) (fun i => (xs i).1) (fun i => (xs i).2) := by
    rw [RelEffCartierDiv.restrictToOpen_I, hfull]
    exact RelEffCartierDiv.prodKerGraph_comap_openProdMap c U xs
  have hvalues (i : Fin n) :
      vK (NeronModelInfra.schemeHomOverComp (xs i) qK) =
        vL (NeronModelInfra.schemeHomOverComp (xsL i) qL') := by
    change Additive.ofMul
      (adj.homEquiv T G.X
        (divisorScalarExtensionPoint c D L (extendedPoints i) ≫ q)) =
      Additive.ofMul (extendedPoints i ≫ qL)
    exact congrArg Additive.ofMul
      (modulusGroupMapScalarExtension_point c D L G q (extendedPoints i)).symm
  have hsum :
      vK (supportedDivisorSum c U S.universal S.sum E hE) =
        vL (supportedDivisorSum cL UL SL.universal SL.sum EL hEL) := by
    rw [supportedDivisorSum_evaluate_tuple c U S.universal S.tupleMap
      S.tupleMap_toBase S.tuple_ideal (commGroupRelativeLaw G) qK S.sum S.tuple_sum
      (T.hom ≫ specMap K L) xs E hE hopen,
      supportedDivisorSum_evaluate_tuple cL UL SL.universal SL.tupleMap
        SL.tupleMap_toBase SL.tuple_ideal (commGroupRelativeLaw extendedGroup)
        qL' SL.sum SL.tuple_sum
        T.hom xsL EL hEL hopenL,
      (commGroupRelativeLaw G).value_sumList (T.hom ≫ specMap K L) vK hvK₁ hvK₂,
      (commGroupRelativeLaw extendedGroup).value_sumList T.hom vL
        (commGroupPointValue_one extendedGroup T.hom) (commGroupPointValue_mul extendedGroup T.hom),
      List.map_ofFn, List.map_ofFn]
    exact congrArg (fun f : Fin n → Additive (T ⟶ extendedGroup.X) => (List.ofFn f).sum)
      (funext hvalues)
  have hbase :
      vK (GoodReductionJacobian.schemeHomOverComp (T.hom ≫ specMap K L)
        (Category.comp_id _) (GoodReductionJacobian.schemeHomOverComp
          ε.left (Over.w ε) qK)) =
      vL (GoodReductionJacobian.schemeHomOverComp T.hom (Category.comp_id _)
        (GoodReductionJacobian.schemeHomOverComp εL.left (Over.w εL) qL')) := by
    have hp := modulusGroupMapScalarExtension_point c D L G q εL
    have he : divisorScalarExtensionPoint c D L εL =
        (Over.homMk (T.hom ≫ specMap K L) (Category.comp_id _) :
          (Over.map (specMap K L)).obj T ⟶
            Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε := by
      exact divisorScalarExtensionPoint_lift c D L _
    rw [he] at hp
    change Additive.ofMul
        (adj.homEquiv T G.X
          ((Over.homMk (T.hom ≫ specMap K L) (Category.comp_id _) :
            (Over.map (specMap K L)).obj T ⟶
              Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε ≫ q)) =
      Additive.ofMul
        ((Over.homMk T.hom (Category.comp_id _) : T ⟶ T) ≫ εL ≫ qL)
    have hid : (Over.homMk T.hom (Category.comp_id _) : T ⟶ T) = 𝟙 T := by
      apply Over.OverMorphism.ext
      rfl
    rw [hid, Category.id_comp]
    exact congrArg Additive.ofMul (by simpa only [Category.assoc] using hp.symm)
  simp only [T, Over.mk_hom] at hbase
  apply (Additive.ofMul : (T ⟶ extendedGroup.X) ≃ Additive (T ⟶ extendedGroup.X)).injective
  change vK (correctedSupportedDivisorSum c U S.universal (commGroupRelativeLaw G)
      S.sum (GoodReductionJacobian.schemeHomOverComp ε.left (Over.w ε) qK) E hE) =
    vL (correctedSupportedDivisorSum cL UL SL.universal (commGroupRelativeLaw extendedGroup)
      SL.sum (GoodReductionJacobian.schemeHomOverComp εL.left (Over.w εL) qL') EL hEL)
  rw [value_correctedSupportedDivisorSum c U S.universal (commGroupRelativeLaw G)
    S.sum (GoodReductionJacobian.schemeHomOverComp ε.left (Over.w ε) qK) E hE
    vK hvK₁ hvK₂,
    value_correctedSupportedDivisorSum cL UL SL.universal (commGroupRelativeLaw extendedGroup)
      SL.sum (GoodReductionJacobian.schemeHomOverComp εL.left (Over.w εL) qL') EL hEL
      vL (commGroupPointValue_one extendedGroup T.hom)
      (commGroupPointValue_mul extendedGroup T.hom),
    hsum, hbase]

end AlgebraicGeometry.GeneralizedJacobian
