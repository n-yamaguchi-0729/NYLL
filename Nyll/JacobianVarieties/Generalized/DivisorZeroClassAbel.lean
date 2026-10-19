/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorZeroClassRigidification
import Nyll.JacobianVarieties.Generalized.ModulusClassAbel

/-! # The concrete divisor comparison preserves the full-modulus Abel class -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) [GeometricallyIntegral M.toBase]
  (I : M.C.IdealSheafData) (hI : I.IsInvertible) (𝒱 : M.C.TwoAffineOpenCover)

/-- The actual divisor-class Abel point is sent to the quotient of the two
canonically normalized point bundles, with the full modulus trivializations. -/
theorem rigidifiedZeroClassEquiv_classAbel
    (v₀ w : Place K F) (h₀ : M.cartierModulus I hI v₀ = 0)
    (hw : M.cartierModulus I hI w = 0) :
    (M.rigidifiedZeroClassEquiv I hI 𝒱
      ((M.cartierModulus I hI).classAbel v₀ h₀ (M.place_deg_eq_one v₀) w)).1 =
        Additive.ofMul
          (classOf (M.rigidifiedPointBundle I hI w hw) /
            classOf (M.rigidifiedPointBundle I hI v₀ h₀)) := by
  rw [(M.cartierModulus I hI).classAbel_of_away v₀ h₀ (M.place_deg_eq_one v₀) w hw,
    M.rigidifiedZeroClassEquiv_mkZero I hI 𝒱]
  change M.rigidifiedDivisorHom I hI
    (Finsupp.single w 1 - Divisor.degree (Finsupp.single w 1) • Finsupp.single v₀ 1) = _
  rw [Divisor.degree_single, M.place_deg_eq_one w, Int.natCast_one, mul_one, one_zsmul]
  exact M.rigidifiedDivisorHom_point_difference I hI w v₀ hw h₀

end AlgebraicCurve.CurveModel
