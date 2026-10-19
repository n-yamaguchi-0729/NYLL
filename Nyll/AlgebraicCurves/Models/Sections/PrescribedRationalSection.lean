/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.RationalPresentationGlobalSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.RationalSectionPresentationRatio
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealDivisorRangeInvModuleEqLSpaceOn
import Nyll.AlgebraicCurves.Models.Divisors.CartierGeneratorOrder
import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
import Nyll.AlgebraicCurves.Places.Restriction.PlaceEquivOrdEqEllMapDomainEq
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions

/-! # A prescribed rational function with a Cartier pole bound gives an actual section -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem transportedPlace_stalkRange
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F)
    (π : letI := M.functionFieldAlgebra; Place K F ≃ Place K M.C.functionField)
    (hπ : letI := M.functionFieldAlgebra
      ∀ w : Place K F, ((π w).toValuationSubring : Set M.C.functionField) =
        M.ffAlgEquiv '' (w.toValuationSubring : Set F)) (x : closedPoints M.C) :
    let := M.functionFieldAlgebra
    (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField).range =
      (π (M.placeOfPoint x)).toValuationSubring.toSubring := by
  let := M.functionFieldAlgebra
  apply SetLike.coe_injective
  change Set.range (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) =
    ((π (M.placeOfPoint x)).toValuationSubring : Set M.C.functionField)
  have he : ((M.placeOfPoint x).toValuationSubring : Set F) =
      M.ffEquiv.symm '' Set.range (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) := by
    rw [← Set.range_comp]
    exact (congrArg (fun S : Subring F => (S : Set F)) (M.range_stalk_eq x)).symm
  have h := hπ (M.placeOfPoint x)
  rw [he, Set.image_image] at h
  simpa only [Function.comp_def, M.ffAlgEquiv_apply, RingEquiv.apply_symm_apply,
    Set.image_id'] using h.symm

/-- A nonzero rational function with the actual Cartier pole bound lifts to an
actual global inverse-ideal section. Every affine frame computes the prescribed function. -/
theorem exists_section_of_cartier_pole_bound
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F) (J : M.C.IdealSheafData) (hJ : J.IsInvertible)
    (f : F) (hf : f ≠ 0)
    (hpole : ∀ w : Place K F, 0 ≤ w.ord f + (M.cartierModulus J hJ w : ℤ)) :
    ∃ s : 𝟙_ M.C.Modules ⟶ J.invModule, s ≠ 0 ∧
      ∀ (U : M.C.affineOpens) [Nonempty U.1]
        (τ : J.invModule.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        f = M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff s U.1 τ.hom)) /
          M.ffEquiv.symm (M.C.germToFunctionField U.1
            (coeff J.invModuleSection U.1 τ.hom)) := by
  classical
  let := M.functionFieldAlgebra
  obtain ⟨E, φ, ⟨hnat, hsmul, hinj, hrange, _horder⟩, hc₀, hpin⟩ :=
    Scheme.IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn M.toBase hJ
  let c₀ := φ ⊤ (J.invModuleSection.app ⊤ (toUnitSection ⊤ 1))
  have hc : c₀ ≠ 0 := hc₀
  obtain ⟨π, hπrange, hπord, _hπdeg, _hπell, _hπdegree, _hπprincipal⟩ :=
    exists_placeEquiv_ord_eq_and_ell_mapDomain_eq M.ffAlgEquiv
  have hcoeff (w : Place K F) :
      E (π w) + (π w).ord c₀ = (M.cartierModulus J hJ w : ℤ) := by
    let x := M.placeEquiv.symm w
    have hwx : M.placeOfPoint x = w := M.placeEquiv.apply_symm_apply w
    have hr : (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField).range =
        (π w).toValuationSubring.toSubring := by
      rw [← hwx]
      exact transportedPlace_stalkRange M π hπrange x
    obtain ⟨U, r, hxr, g, _hg, hJg⟩ := hJ x.1
    let V : M.C.affineOpens := M.C.affineBasicOpen r
    have hVx : x.1 ∈ V.1 := hxr
    let : Nonempty V.1 := ⟨⟨x.1, hVx⟩⟩
    have hcE := hpin V.1 V.2 g x.1 hVx x.property hJg (π w) hr
    have hgord : (π w).ord (algebraMap Γ(M.C, V.1) M.C.functionField g) =
        w.ord (M.ffEquiv.symm (M.C.germToFunctionField V.1 g)) := by
      change (π w).ord (M.C.germToFunctionField V.1 g) = _
      simpa only [M.ffAlgEquiv_apply, RingEquiv.apply_symm_apply] using
        hπord w (M.ffEquiv.symm (M.C.germToFunctionField V.1 g))
    have ho := M.ord_affineGenerator J hJ V.1 V.2 g hJg x hVx
    rw [hwx] at ho
    exact hcE.trans (hgord.trans ho)
  have hf' : M.ffEquiv f ≠ 0 := fun h => hf
    (M.ffEquiv.injective (h.trans (map_zero M.ffEquiv).symm))
  let value := M.ffEquiv f * c₀
  have hvalue_ne : value ≠ 0 := mul_ne_zero hf' hc
  have hlocal (U : M.C.Opens) (hU : IsAffineOpen U) (hUne : Nonempty U) :
      value ∈ Set.range (φ U) := by
    rw [hrange U hU hUne]
    intro v _hv
    obtain ⟨w, rfl⟩ := π.surjective v
    apply (π w).adicValuation_le_exp_iff.mpr
    right
    have ho : (π w).ord value = w.ord f + (π w).ord c₀ :=
      ((π w).ord_mul hf' hc).trans
        (congrArg (· + (π w).ord c₀) (hπord w f))
    have hb := hpole w
    have he := hcoeff w
    omega
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_globalSection_of_affine_mem_range
    J.invModule φ hnat hinj value hlocal
  have hsne : s ≠ 0 := by
    intro hz
    have h := hs
    rw [hz, Scheme.Modules.Hom.zero_app] at h
    change φ ⊤ 0 = value at h
    rw [map_zero] at h
    exact hvalue_ne h.symm
  refine ⟨s, hsne, ?_⟩
  intro U hU τ
  have hq : φ ⊤ (s.app ⊤ (toUnitSection ⊤ 1)) / c₀ = M.ffEquiv f :=
    (congrArg (· / c₀) hs).trans (mul_div_cancel_right₀ _ hc)
  have hr := Scheme.Modules.presentation_ratio_eq_coeff_ratio J.invModule φ hnat hsmul hinj
    s J.invModuleSection U τ
  have he : M.ffEquiv f = M.C.germToFunctionField U.1 (coeff s U.1 τ.hom) /
      M.C.germToFunctionField U.1 (coeff J.invModuleSection U.1 τ.hom) := hq.symm.trans hr
  exact (M.ffEquiv.symm_apply_apply f).symm.trans
    ((congrArg M.ffEquiv.symm he).trans (map_div₀ M.ffEquiv.symm _ _))

end AlgebraicCurve.CurveModel
