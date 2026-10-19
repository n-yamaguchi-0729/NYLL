/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Sections.SectionRatioCongruence
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.SectionVanishingClosedSubscheme
import Nyll.SchemeTheory.Divisors.StalkIdealExt

/-! # Full place congruence forces equality on the original modulus -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

/-- A ratio of two actual stalk units is congruent to one precisely when
their difference lies in the full Cartier stalk ideal. -/
theorem congruentOne_stalkUnit_ratio_iff (x : closedPoints M.C)
    (a b : (M.C.presheaf.stalk x.1)ˣ) :
    (M.placeOfPoint x).CongruentOne (M.cartierMultiplicity I hI x)
        (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a) /
          M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField b)) ↔
      (a : M.C.presheaf.stalk x.1) - (b : M.C.presheaf.stalk x.1) ∈ I.stalkIdeal x.1 := by
  let r : M.C.presheaf.stalk x.1 →+* F := M.ffEquiv.symm.toRingHom.comp
    (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)
  have hinv : r ((b⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1) = (r b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  have hfield : M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField
        ((a * b⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1)) =
      M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a) /
        M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField b) := by
    change r ((a * b⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1) = r a / r b
    rw [Units.val_mul, map_mul, hinv, div_eq_mul_inv]
  rw [← hfield, M.congruentOne_stalkUnit_iff,
    ← M.stalkIdeal_eq_maximalIdeal_pow I hI x]
  constructor
  · intro h
    have hm := (I.stalkIdeal x.1).mul_mem_right (b : M.C.presheaf.stalk x.1) h
    rw [Units.val_mul, sub_mul, mul_assoc, Units.inv_mul, mul_one, one_mul] at hm
    exact hm
  · intro h
    have hm := (I.stalkIdeal x.1).mul_mem_right
      ((b⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1) h
    rw [sub_mul, Units.mul_inv] at hm
    exact hm

/-- A global rational ratio satisfying the original full place modulus
identifies the restrictions of its two sections on the entire closed scheme. -/
theorem pullbackSection_eq_of_congruentOne_ratio
    {L : M.C.Modules} (hL : Scheme.Modules.IsInvertible L)
    (s t : 𝟙_ M.C.Modules ⟶ L) (f : F)
    (hf : (M.cartierModulus I hI).CongruentOne f)
    (hratio : ∀ (U : M.C.affineOpens) [Nonempty U.1]
      (τ : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
      f = M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff s U.1 τ.hom)) /
        M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff t U.1 τ.hom)))
    (hsI : ∀ z : I.subscheme, I.subschemeι z ∉ (zeroSchemeIdeal s).support)
    (htI : ∀ z : I.subscheme, I.subschemeι z ∉ (zeroSchemeIdeal t).support) :
    pullbackSection I.subschemeι s = pullbackSection I.subschemeι t := by
  apply (hL.pullbackSection_eq_iff_zeroSchemeIdeal_sub_le I s t).mpr
  apply Scheme.IdealSheafData.le_iff_stalkIdeal_le.mpr
  intro y
  by_cases hy : y ∈ I.support
  · have hyrange : y ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hy
    obtain ⟨z, rfl⟩ := hyrange
    let x : closedPoints M.C := ⟨I.subschemeι z, M.isClosed_cartierPoint I hI z⟩
    obtain ⟨U, hxU, _hUtop, ⟨τ⟩⟩ := hL.exists_restrict_iso (V := ⊤) (x := x.1) trivial
    have : Nonempty U.1 := ⟨⟨x.1, hxU⟩⟩
    obtain ⟨a, ha⟩ := hL.isUnit_coeff_germ_of_notMem_support s U τ x.1 hxU (hsI z)
    obtain ⟨b, hb⟩ := hL.isUnit_coeff_germ_of_notMem_support t U τ x.1 hxU (htI z)
    have hxmod : M.cartierModulus I hI (M.placeOfPoint x) ≠ 0 := by
      rw [M.cartierModulus_placeOfPoint I hI x]
      intro hz
      exact (M.cartierMultiplicity_eq_zero_iff I hI x).mp hz hy
    have hc := hf.2 (M.placeOfPoint x) hxmod
    rw [M.cartierModulus_placeOfPoint I hI x, hratio U τ] at hc
    have hmem : (a : M.C.presheaf.stalk x.1) - (b : M.C.presheaf.stalk x.1) ∈
        I.stalkIdeal x.1 := by
      apply (M.congruentOne_stalkUnit_ratio_iff I hI x a b).mp
      simpa only [ha, hb, M.C.algebraMap_germ_eq_germToFunctionField hxU] using hc
    rw [(zeroSchemeIdeal (s - t)).stalkIdeal_eq_map_ideal x.1 U hxU,
      ((hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq (s - t)).2 U τ).1,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
      coeff_sub, map_sub]
    simpa only [ha, hb] using hmem
  · rw [(I.stalkIdeal_eq_top_iff_notMem_support y).mpr hy]
    exact le_top

end AlgebraicCurve.CurveModel
