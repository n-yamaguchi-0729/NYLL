/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveFormalTranslation
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Polynomial.Taylor

/-! # A finite simple-root equation for an actual formal translation

The minimal polynomial over the canonical separating subfield is transported
back to `RatFunc K` and its denominators are cleared over `Polynomial K`.
Translating the coefficient variable by the actual curve parameter and the
root variable by the given function produces a polynomial in two variables.
Its formal root is the translated function minus its constant term. At the
origin its linear coefficient is a nonzero scalar times the derivative of
the original separable minimal polynomial.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Every function has an actual finite polynomial equation for its formal
translation minus its constant term, with a simple root at the origin. -/
theorem exists_formalTranslation_simple_polynomial
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (q : F) :
    ∃ P : Polynomial (Polynomial F),
      (P.coeff 0).coeff 0 = 0 ∧ (P.coeff 1).coeff 0 ≠ 0 ∧
        (P.map Polynomial.coeToPowerSeries.ringHom).eval (σ q - PowerSeries.C q) = 0 := by
  let R : IntermediateField K F := IntermediateField.adjoin K {t}
  let e : RatFunc K ≃ₐ[K] R := RatFunc.algEquivOfTranscendental t ht
  let β : RatFunc K →ₐ[K] F := R.val.comp e.toAlgHom
  let p : Polynomial R := minpoly R q
  let pRat : Polynomial (RatFunc K) := p.map e.symm.toAlgHom.toRingHom
  let Q : Polynomial (Polynomial K) :=
    IsLocalization.integerNormalization (nonZeroDivisors (Polynomial K)) pRat
  obtain ⟨b, hb, hQ⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial K)) pRat
  change Q.map (algebraMap (Polynomial K) (RatFunc K)) = b • pRat at hQ
  rw [← IsScalarTower.algebraMap_smul (RatFunc K) b pRat,
    Polynomial.smul_eq_C_mul] at hQ
  have hβpoly : β.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) =
      (Polynomial.aeval t : Polynomial K →ₐ[K] F).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, RatFunc.algebraMap_C,
        Polynomial.aeval_C, RatFunc.algebraMap_eq_C] using β.commutes a
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, RatFunc.algebraMap_X,
        Polynomial.aeval_X]
      change ((e RatFunc.X : R) : F) = t
      exact RatFunc.algEquivOfTranscendental_X t ht
  have hβe : β.toRingHom.comp e.symm.toAlgHom.toRingHom = algebraMap R F := by
    apply RingHom.ext
    intro x
    change ((e (e.symm x) : R) : F) = (x : F)
    exact congrArg (fun y : R => (y : F)) (e.apply_symm_apply x)
  let a : F := β (algebraMap (Polynomial K) (RatFunc K) b)
  have ha : a ≠ 0 := by
    apply (map_ne_zero β).mpr
    intro h
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    exact (RatFunc.algebraMap_injective K) (h.trans (map_zero _).symm)
  let P₀ : Polynomial F := Q.map (Polynomial.aeval t : Polynomial K →ₐ[K] F).toRingHom
  have hP₀ : P₀ = Polynomial.C a * p.map (algebraMap R F) := by
    have h := congrArg (Polynomial.map β.toRingHom) hQ
    simp only [Polynomial.map_map, hβpoly, Polynomial.map_mul, Polynomial.map_C,
      pRat, hβe] at h
    simpa only [P₀, a, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  have hroot₀ : P₀.eval q = 0 := by
    rw [hP₀, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map]
    change a * Polynomial.aeval q (minpoly R q) = 0
    rw [minpoly.aeval, mul_zero]
  have hder₀ : P₀.derivative.eval q ≠ 0 := by
    rw [hP₀, Polynomial.derivative_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.derivative_map, Polynomial.eval_map]
    exact mul_ne_zero ha ((Algebra.IsSeparable.isSeparable R q).aeval_derivative_ne_zero
      (minpoly.aeval R q))
  let tr : Polynomial K →ₐ[K] Polynomial F :=
    Polynomial.aeval (Polynomial.C t + Polynomial.X)
  have htr : Polynomial.coeToPowerSeries.ringHom.comp tr.toRingHom =
      σ.toRingHom.comp (Polynomial.aeval t : Polynomial K →ₐ[K] F).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, tr, Polynomial.aeval_C,
        Polynomial.algebraMap_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, AlgHom.commutes, PowerSeries.algebraMap_apply]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, tr, Polynomial.aeval_X,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_add, Polynomial.coe_C,
        Polynomial.coe_X, hσt]
  have hcc : PowerSeries.constantCoeff.comp
      (Polynomial.coeToPowerSeries.ringHom : Polynomial F →+* PowerSeries F) =
      Polynomial.constantCoeff := by
    apply RingHom.ext
    intro f
    exact Polynomial.constantCoeff_coe f
  have htr₀ : Polynomial.constantCoeff.comp tr.toRingHom =
      (Polynomial.aeval t : Polynomial K →ₐ[K] F).toRingHom := by
    rw [← hcc, RingHom.comp_assoc, htr, ← RingHom.comp_assoc, hσ0, RingHom.id_comp]
  let H : Polynomial (Polynomial F) := Q.map tr.toRingHom
  have hH : H.map Polynomial.coeToPowerSeries.ringHom = P₀.map σ.toRingHom := by
    change (Q.map tr.toRingHom).map Polynomial.coeToPowerSeries.ringHom =
      (Q.map (Polynomial.aeval t : Polynomial K →ₐ[K] F).toRingHom).map σ.toRingHom
    rw [Polynomial.map_map, Polynomial.map_map, htr]
  have hH₀ : H.map Polynomial.constantCoeff = P₀ := by
    change (Q.map tr.toRingHom).map Polynomial.constantCoeff = P₀
    rw [Polynomial.map_map, htr₀]
  have hHroot : (H.map Polynomial.coeToPowerSeries.ringHom).eval (σ q) = 0 := by
    rw [hH, Polynomial.eval_map]
    change Polynomial.eval₂ σ.toRingHom (σ.toRingHom q) P₀ = 0
    rw [Polynomial.eval₂_at_apply (p := P₀) σ.toRingHom q, hroot₀, map_zero]
  let P : Polynomial (Polynomial F) := Polynomial.taylor (Polynomial.C q) H
  have hccq : Polynomial.constantCoeff (Polynomial.C q) = q := Polynomial.coeff_C_zero
  have hP₀shift : P.map Polynomial.constantCoeff = Polynomial.taylor q P₀ := by
    change (Polynomial.taylor (Polynomial.C q) H).map Polynomial.constantCoeff = _
    rw [Polynomial.map_taylor, hH₀, hccq]
  refine ⟨P, ?_, ?_, ?_⟩
  · have h := congrArg (fun f : Polynomial F => f.coeff 0) hP₀shift
    have hz : (P.coeff 0).coeff 0 = P₀.eval q := by
      simpa only [Polynomial.coeff_map, Polynomial.constantCoeff_apply,
        Polynomial.taylor_coeff_zero] using h
    exact hz.trans hroot₀
  · have h := congrArg (fun f : Polynomial F => f.coeff 1) hP₀shift
    have hz : (P.coeff 1).coeff 0 = P₀.derivative.eval q := by
      simpa only [Polynomial.coeff_map, Polynomial.constantCoeff_apply,
        Polynomial.taylor_coeff_one] using h
    rw [hz]
    exact hder₀
  · change ((Polynomial.taylor (Polynomial.C q) H).map
        Polynomial.coeToPowerSeries.ringHom).eval (σ q - PowerSeries.C q) = 0
    rw [Polynomial.map_taylor, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
      Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, sub_add_cancel]
    exact hHroot

end AlgebraicCurve
