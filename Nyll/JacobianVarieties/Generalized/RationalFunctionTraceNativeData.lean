/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceAffineLine
import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparableRationalCoordinate
import Nyll.AlgebraicCurves.Models.Charts.IsoTwoAffineLineCover

/-! # Native field data of the actual reciprocal trace

The actual rational-coordinate map supplies the finite separable algebra
on the original scheme function fields. Its reciprocal is a rational base
coordinate whose image is exactly the contact function. No replacement of
the finite curve map or its Cartier family is involved.
-/

noncomputable section

universe u

open AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Models.Proofs.CurveModel_exists_iso_of_twoAffineLineCover

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral

/-- The prescribed separating coordinate induces the actual finite separable
native field extension and a rational coordinate for its reciprocal. -/
theorem reciprocalTrace_native_field_data
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (P : CurveModel K (RatFunc K)) (M : CurveModel K F)
    (φ : RatFunc K →ₐ[K] F)
    (htr : Transcendental K (φ RatFunc.X))
    [FiniteDimensional (IntermediateField.adjoin K {φ RatFunc.X}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {φ RatFunc.X}) F]
    (g : Fˣ) (hφX : φ RatFunc.X = ((g : F) - 1)⁻¹) :
    let _ := P.functionFieldAlgebra
    let _ := M.functionFieldAlgebra
    let ψ : P.C.functionField →ₐ[K] M.C.functionField :=
      (M.ffAlgEquiv.toAlgHom.comp φ).comp P.ffAlgEquiv.symm.toAlgHom
    let _ : Algebra P.C.functionField M.C.functionField := ψ.toRingHom.toAlgebra
    IsScalarTower K P.C.functionField M.C.functionField ∧
      FiniteDimensional P.C.functionField M.C.functionField ∧
      Algebra.IsSeparable P.C.functionField M.C.functionField ∧
      ∃ p : RatFunc K ≃ₐ[K] P.C.functionField,
        p RatFunc.X = P.ffAlgEquiv (RatFunc.X⁻¹) ∧
        algebraMap P.C.functionField M.C.functionField (p RatFunc.X) =
          M.ffAlgEquiv ((g : F) - 1) := by
  intro algKB algKF ψ algBF
  let algRF : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  obtain ⟨hfinite, hseparable⟩ :=
    FunctionField.finite_separable_ratFuncMap_of_parameter φ htr
  have : FiniteDimensional (RatFunc K) F := hfinite
  have : Algebra.IsSeparable (RatFunc K) F := hseparable
  have hsquare :
      (algebraMap P.C.functionField M.C.functionField).comp P.ffEquiv.toRingHom =
        M.ffEquiv.toRingHom.comp (algebraMap (RatFunc K) F) := by
    apply RingHom.ext
    intro f
    change M.ffAlgEquiv (φ (P.ffAlgEquiv.symm (P.ffAlgEquiv f))) = M.ffAlgEquiv (φ f)
    rw [P.ffAlgEquiv.symm_apply_apply]
  have htower : IsScalarTower K P.C.functionField M.C.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (ψ.commutes a).symm
  have hfiniteNative : FiniteDimensional P.C.functionField M.C.functionField :=
    Module.Finite.of_equiv_equiv P.ffEquiv M.ffEquiv hsquare
  have hsepNative : Algebra.IsSeparable P.C.functionField M.C.functionField :=
    Algebra.IsSeparable.of_equiv_equiv P.ffEquiv M.ffEquiv hsquare
  obtain ⟨σ, hσ, _⟩ := E86P1.exists_algEquiv_ratFunc_inv K
  refine ⟨htower, hfiniteNative, hsepNative, σ.trans P.ffAlgEquiv, ?_, ?_⟩
  · change P.ffAlgEquiv (σ RatFunc.X) = _
    rw [hσ]
  · change M.ffAlgEquiv (φ (P.ffAlgEquiv.symm (P.ffAlgEquiv (σ RatFunc.X)))) = _
    rw [P.ffAlgEquiv.symm_apply_apply, hσ, map_inv₀, hφX, inv_inv]

end AlgebraicGeometry.GeneralizedJacobian
