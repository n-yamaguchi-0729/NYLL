/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusIdentityDivisorComparison
import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorKernelForward
import Nyll.JacobianVarieties.Generalized.ModulusEvaluation

/-! # Modulus invariance of corrected actual divisor evaluations -/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual full divisor class maps to the inverse image of its raw family class. -/
theorem rigidifiedDivisorHom_supportedFamily {n : ℕ}
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K))))
    (hE : E.SupportedIn (modulusComplement (modulusCurveMap D))) :
    M.rigidifiedDivisorHom (modulusCurveIdeal D) (modulusCurveIdeal_isInvertible D)
        (M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)).toDivisor =
      Additive.ofMul ((closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)).symm
        (modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E hE)) := by
  rw [M.rigidifiedDivisorHom_cartierModulus (modulusCurveIdeal D)
    (modulusCurveIdeal_isInvertible D) (modulusCurveIdeal E)
    (modulusCurveIdeal_isInvertible E) (modulusCurveIdeal_avoids M.toBase (modulusCurveMap D) E hE)]
  apply congrArg Additive.ofMul
  apply (closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)).injective
  rw [MulEquiv.apply_symm_apply]
  exact closedModulusIdentityClassesEquiv_ofDivisor M.toBase (modulusCurveMap D) E hE

/-- Equality of the actual corrected classes forces equality of evaluations for a map
with the full modulus. The correction permits different degrees on the two charts. -/
theorem divisorEvaluation_sub_nsmul_eq_of_familyClass_div_pow_eq
    {A : Type w} [AddCommGroup A] (a : Place K F → A)
    (ha : (M.cartierModulus (modulusCurveIdeal D)
      (modulusCurveIdeal_isInvertible D)).HasModulus a)
    {r₀ r₁ rP : ℕ}
    (E₀ : RelEffCartierDiv M.toBase r₀ (𝟙 (Spec (CommRingCat.of K))))
    (h₀ : E₀.SupportedIn (modulusComplement (modulusCurveMap D)))
    (E₁ : RelEffCartierDiv M.toBase r₁ (𝟙 (Spec (CommRingCat.of K))))
    (h₁ : E₁.SupportedIn (modulusComplement (modulusCurveMap D)))
    (P : RelEffCartierDiv M.toBase rP (𝟙 (Spec (CommRingCat.of K))))
    (hP : P.SupportedIn (modulusComplement (modulusCurveMap D))) (n₀ n₁ : ℕ)
    (he : modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E₀ h₀ /
        modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n₀ =
      modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E₁ h₁ /
        modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n₁) :
    Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal E₀) (modulusCurveIdeal_isInvertible E₀)).toDivisor -
      n₀ • Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor =
    Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal E₁) (modulusCurveIdeal_isInvertible E₁)).toDivisor -
      n₁ • Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor := by
  let I := modulusCurveIdeal D
  have hI : I.IsInvertible := modulusCurveIdeal_isInvertible D
  let V₀ : (M.cartierModulus I hI).divAway :=
    ⟨(M.cartierModulus (modulusCurveIdeal E₀) (modulusCurveIdeal_isInvertible E₀)).toDivisor,
      M.cartierModulus_toDivisor_mem_divAway I hI (modulusCurveIdeal E₀)
        (modulusCurveIdeal_isInvertible E₀)
        (modulusCurveIdeal_avoids M.toBase (modulusCurveMap D) E₀ h₀)⟩
  let V₁ : (M.cartierModulus I hI).divAway :=
    ⟨(M.cartierModulus (modulusCurveIdeal E₁) (modulusCurveIdeal_isInvertible E₁)).toDivisor,
      M.cartierModulus_toDivisor_mem_divAway I hI (modulusCurveIdeal E₁)
        (modulusCurveIdeal_isInvertible E₁)
        (modulusCurveIdeal_avoids M.toBase (modulusCurveMap D) E₁ h₁)⟩
  let VP : (M.cartierModulus I hI).divAway :=
    ⟨(M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor,
      M.cartierModulus_toDivisor_mem_divAway I hI (modulusCurveIdeal P)
        (modulusCurveIdeal_isInvertible P)
        (modulusCurveIdeal_avoids M.toBase (modulusCurveMap D) P hP)⟩
  have he' := congrArg (fun x => Additive.ofMul
    ((closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)).symm x)) he
  simp only [map_div, map_pow, ofMul_div, ofMul_pow] at he'
  have hk : M.rigidifiedDivisorAwayHom I hI ((V₀ - n₀ • VP) - (V₁ - n₁ • VP)) = 0 := by
    change M.rigidifiedDivisorHom I hI
      ((V₀.1 - n₀ • VP.1) - (V₁.1 - n₁ • VP.1)) = 0
    simp only [map_sub, map_nsmul]
    rw [M.rigidifiedDivisorHom_supportedFamily D E₀ h₀,
      M.rigidifiedDivisorHom_supportedFamily D E₁ h₁,
      M.rigidifiedDivisorHom_supportedFamily D P hP]
    exact sub_eq_zero.mpr he'
  have hp := M.rigidifiedDivisorAwayHom_ker_le_principal I hI
    ((V₀ - n₀ • VP) - (V₁ - n₁ • VP)) hk
  have hv := ha.evaluation_eq_zero hp
  change Divisor.evaluation a ((V₀.1 - n₀ • VP.1) - (V₁.1 - n₁ • VP.1)) = 0 at hv
  simp only [map_sub, map_nsmul] at hv
  exact sub_eq_zero.mp hv

end AlgebraicCurve.CurveModel
