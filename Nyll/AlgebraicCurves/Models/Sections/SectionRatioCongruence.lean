/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Divisors.CartierModulusRestriction
import Nyll.AlgebraicCurves.Models.Sections.RationalSectionRatio
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionDifferenceIdeal
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Ratios of equally rigidified sections satisfy the full modulus -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

/-- If two sections have equal restrictions to the actual modulus, then their
local coefficient ratio is congruent to one to its full Cartier order wherever
both sections are nonvanishing. -/
theorem congruentOne_coeff_ratio_of_pullback_eq
    {L : M.C.Modules} (hL : Scheme.Modules.IsInvertible L)
    (s t : 𝟙_ M.C.Modules ⟶ L)
    (hst : pullbackSection I.subschemeι s = pullbackSection I.subschemeι t)
    (U : M.C.affineOpens)
    (τ : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (x : closedPoints M.C) (hx : x.1 ∈ U.1)
    (hs : x.1 ∉ (zeroSchemeIdeal s).support)
    (ht : x.1 ∉ (zeroSchemeIdeal t).support) :
    let _ : Nonempty U.1 := ⟨⟨x.1, hx⟩⟩
    (M.placeOfPoint x).CongruentOne (M.cartierMultiplicity I hI x)
      (M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff s U.1 τ.hom)) /
        M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff t U.1 τ.hom))) := by
  let : Nonempty U.1 := ⟨⟨x.1, hx⟩⟩
  obtain ⟨a, ha⟩ := hL.isUnit_coeff_germ_of_notMem_support s U τ x.1 hx hs
  obtain ⟨b, hb⟩ := hL.isUnit_coeff_germ_of_notMem_support t U τ x.1 hx ht
  have hdiff : (a : M.C.presheaf.stalk x.1) - (b : M.C.presheaf.stalk x.1) ∈
      I.stalkIdeal x.1 := by
    rw [ha, hb]
    exact hL.coeff_germ_sub_mem_stalkIdeal_of_pullback_eq I s t hst U τ.hom x.1 hx
  have hunit : ((a * b⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1) - 1 ∈
      IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^
        M.cartierMultiplicity I hI x := by
    rw [← M.stalkIdeal_eq_maximalIdeal_pow I hI x]
    have h := (I.stalkIdeal x.1).mul_mem_right
      ((b⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1) hdiff
    rw [sub_mul, Units.mul_inv] at h
    exact h
  have hc := (M.congruentOne_stalkUnit_iff x
    (M.cartierMultiplicity I hI x) (a * b⁻¹)).mpr hunit
  have hinv : algebraMap (M.C.presheaf.stalk x.1) M.C.functionField
        ((b⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1) =
      (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  simp only [Units.val_mul, map_mul, hinv, map_inv₀, ha, hb,
    M.C.algebraMap_germ_eq_germToFunctionField hx] at hc
  simpa only [div_eq_mul_inv] using hc

/-- Two nonzero sections normalized equally on the full modulus have a
single global rational ratio satisfying the original place congruences. -/
theorem exists_congruentOne_rationalSectionRatio
    {L : M.C.Modules} (hL : Scheme.Modules.IsInvertible L)
    (s t : 𝟙_ M.C.Modules ⟶ L) (hs : s ≠ 0) (ht : t ≠ 0)
    (hst : pullbackSection I.subschemeι s = pullbackSection I.subschemeι t)
    (hsI : ∀ z : I.subscheme, I.subschemeι z ∉ (zeroSchemeIdeal s).support)
    (htI : ∀ z : I.subscheme, I.subschemeι z ∉ (zeroSchemeIdeal t).support) :
    ∃ f : F, (M.cartierModulus I hI).CongruentOne f ∧
      ∀ (U : M.C.affineOpens) [Nonempty U.1]
        (τ : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        f = M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff s U.1 τ.hom)) /
          M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff t U.1 τ.hom)) := by
  obtain ⟨f, hf, hratio⟩ := M.exists_rationalSectionRatio hL s t hs ht
  refine ⟨f, ⟨hf, ?_⟩, hratio⟩
  intro w hw
  let x := M.placeEquiv.symm w
  have hxI : x.1 ∈ I.support := by
    by_contra hx
    exact hw ((M.cartierModulus_eq_zero_iff I hI w).mpr hx)
  have hxrange : x.1 ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hxI
  obtain ⟨z, hzx⟩ := hxrange
  obtain ⟨U, hxU, _hUtop, ⟨τ⟩⟩ := hL.exists_restrict_iso (V := ⊤) (x := x.1) trivial
  have : Nonempty U.1 := ⟨⟨x.1, hxU⟩⟩
  have hc := M.congruentOne_coeff_ratio_of_pullback_eq I hI hL s t hst U τ x hxU
    (hzx ▸ hsI z) (hzx ▸ htI z)
  change (M.placeOfPoint x).CongruentOne (M.cartierMultiplicity I hI x)
    (M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff s U.1 τ.hom)) /
      M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff t U.1 τ.hom))) at hc
  have hwx : M.placeOfPoint x = w := M.placeEquiv.apply_symm_apply w
  rw [← M.cartierModulus_placeOfPoint I hI x, hwx, ← hratio U τ] at hc
  exact hc

end AlgebraicCurve.CurveModel
