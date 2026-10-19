/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorClassPoints
import Nyll.JacobianVarieties.Generalized.ModulusClassUniversality
import Nyll.JacobianVarieties.Generalized.ModulusDivisorEvaluationInvariance
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveTwoAffineCover

/-! # Actual generalized Jacobian points and corrected divisor evaluation -/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual divisor-class comparison sends each divisor to its original raw class. -/
theorem divisorClassPointEquiv_mkZero_raw
    (E : (M.functionFieldModulus D).divAwayZero) :
    ((rigidifiedZeroClassPointEquiv M.toBase D).symm
      ((M.divisorClassPointEquiv D ((M.functionFieldModulus D).mkZero E)).toMul)).val =
        closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)
          (M.rigidifiedDivisorHom (modulusCurveIdeal D)
            (modulusCurveIdeal_isInvertible D) E.val).toMul :=
  congrArg Subtype.val ((rigidifiedZeroClassPointEquiv M.toBase D).symm_apply_apply _)

/-- The actual full-modulus evaluation on the constructed generalized Jacobian point group. -/
def modulusPointEvaluation {A : Type w} [AddCommGroup A] (a : Place K F → A)
    (ha : (M.functionFieldModulus D).HasModulus a) :
    Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X) →+ A :=
  ha.classEvaluationZero.comp (M.divisorClassPointEquiv D).symm.toAddMonoidHom

/-- A corrected actual supported family evaluates by its genuine degree-zero divisor class. -/
theorem modulusPointEvaluation_correctedFamily
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    {A : Type w} [AddCommGroup A] (a : Place K F → A)
    (ha : (M.functionFieldModulus D).HasModulus a) {r s : ℕ}
    (E : RelEffCartierDiv M.toBase r (𝟙 (Spec (CommRingCat.of K))))
    (hE : E.SupportedIn (modulusComplement (modulusCurveMap D)))
    (P : RelEffCartierDiv M.toBase s (𝟙 (Spec (CommRingCat.of K))))
    (hP : P.SupportedIn (modulusComplement (modulusCurveMap D))) (n : ℕ)
    (hz : modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
      modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n ∈
        modulusPicardZeroSubgroup M.toBase (modulusCurveMap D)
          (Over.mk (𝟙 (Spec (CommRingCat.of K))))) :
    M.modulusPointEvaluation D a ha (Additive.ofMul (rigidifiedZeroClassPointEquiv M.toBase D
      ⟨modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
        modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n, hz⟩)) =
      Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)).toDivisor -
      n • Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor := by
  let I := modulusCurveIdeal D
  have hI : I.IsInvertible := modulusCurveIdeal_isInvertible D
  let V := (SmoothProperCurve.exists_twoAffineOpenCover_of_section K M.toBase ε).choose
  let e := closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)
  let z : modulusPicardZeroSubgroup M.toBase (modulusCurveMap D)
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) :=
    ⟨modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE /
      modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n, hz⟩
  let VE : (M.functionFieldModulus D).divAway :=
    ⟨(M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)).toDivisor,
      M.cartierModulus_toDivisor_mem_divAway I hI (modulusCurveIdeal E)
        (modulusCurveIdeal_isInvertible E)
        (modulusCurveIdeal_avoids M.toBase (modulusCurveMap D) E hE)⟩
  let VP : (M.functionFieldModulus D).divAway :=
    ⟨(M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor,
      M.cartierModulus_toDivisor_mem_divAway I hI (modulusCurveIdeal P)
        (modulusCurveIdeal_isInvertible P)
        (modulusCurveIdeal_avoids M.toBase (modulusCurveMap D) P hP)⟩
  let W := VE - n • VP
  have hW : M.rigidifiedDivisorHom I hI W.val = Additive.ofMul (e.symm z.val) := by
    change M.rigidifiedDivisorHom I hI (VE.val - n • VP.val) = _
    rw [map_sub, map_nsmul, M.rigidifiedDivisorHom_supportedFamily D E hE,
      M.rigidifiedDivisorHom_supportedFamily D P hP]
    simp only [e, z, map_div, map_pow, ofMul_div, ofMul_pow]
  have hdeg : Divisor.degree W.val = 0 := by
    rw [← M.eulerDegree_rigidifiedDivisorAwayHom I hI V W]
    change RigidifiedLineBundle.eulerDegree M.toBase V I.subschemeι
      (M.rigidifiedDivisorHom I hI W.val) = 0
    rw [hW]
    apply (closedModulusIdentityClassesEquiv_mem_zero_iff M.toBase (modulusCurveMap D)
      V (e.symm z.val)).mp
    change e (e.symm z.val) ∈ _
    rw [e.apply_symm_apply]
    exact z.property
  let W₀ : (M.functionFieldModulus D).divAwayZero :=
    ⟨W.val, W.property, Divisor.mem_degZero.mpr hdeg⟩
  have hpoint : M.divisorClassPointEquiv D ((M.functionFieldModulus D).mkZero W₀) =
      Additive.ofMul (rigidifiedZeroClassPointEquiv M.toBase D z) := by
    apply Additive.toMul.injective
    apply (rigidifiedZeroClassPointEquiv M.toBase D).symm.injective
    apply Subtype.ext
    rw [M.divisorClassPointEquiv_mkZero_raw D W₀]
    change e (M.rigidifiedDivisorHom I hI W.val).toMul =
      ((rigidifiedZeroClassPointEquiv M.toBase D).symm
        (rigidifiedZeroClassPointEquiv M.toBase D z)).val
    rw [MulEquiv.symm_apply_apply, hW]
    exact e.apply_symm_apply z.val
  change ha.classEvaluationZero ((M.divisorClassPointEquiv D).symm
    (Additive.ofMul (rigidifiedZeroClassPointEquiv M.toBase D z))) = _
  rw [← hpoint, AddEquiv.symm_apply_apply, ha.classEvaluationZero_mk]
  change Divisor.evaluation a (VE.val - n • VP.val) = _
  rw [map_sub, map_nsmul]

/-- Evaluation on the genuine pointed Abel morphism has its actual basepoint correction. -/
theorem modulusPointEvaluation_abel
    (ε x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
    {A : Type w} [AddCommGroup A] (a : Place K F → A)
    (ha : (M.functionFieldModulus D).HasModulus a) :
    M.modulusPointEvaluation D a ha
        (Additive.ofMul (x ≫ modulusAbelMap M.toBase D ε)) =
      a (M.modulusPlace D x) - a (M.modulusPlace D ε) := by
  rw [← M.divisorClassPointEquiv_abel D ε x]
  change ha.classEvaluationZero ((M.divisorClassPointEquiv D).symm
    (M.divisorClassPointEquiv D _)) = _
  rw [AddEquiv.symm_apply_apply, ha.classEvaluationZero_classAbel_apply
    (M.modulusPlace D ε) (M.functionFieldModulus_modulusPlace_eq_zero D ε)
    (M.place_deg_eq_one (M.modulusPlace D ε)) (M.modulusPlace D x)
    (M.functionFieldModulus_modulusPlace_eq_zero D x),
    M.place_deg_eq_one, Nat.cast_one, one_zsmul]

end AlgebraicCurve.CurveModel
