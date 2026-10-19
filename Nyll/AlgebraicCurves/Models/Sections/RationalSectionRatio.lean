/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleDivisorRangeEqLSpaceOn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleCoeffIdealLeIdealZeroSchemeIdealEq
import Mathlib.AlgebraicGeometry.FunctionField

/-! # A global rational ratio of two nonzero line-bundle sections -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private def sectionValue {X : Scheme.{u}} {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) :
    Γ(L, ⊤) := s.app ⊤ (toUnitSection ⊤ 1)

private theorem sectionValue_res {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (U : X.Opens) :
    L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (sectionValue s) =
      s.app U (toUnitSection U 1) := by
  have hn := ConcreteCategory.congr_hom
    (s.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    (toUnitSection ⊤ 1)
  change s.app U (toUnitSection U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1)) =
    L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (sectionValue s) at hn
  rw [map_one] at hn
  exact hn.symm

private theorem sectionValue_ne_zero {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0) : sectionValue s ≠ 0 := by
  intro hz
  apply hs
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro m
  have hone : s.app U (toUnitSection U 1) = 0 := by
    rw [← sectionValue_res, hz]
    exact (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.map_zero
  have hm : m = (ofUnitSection U m) • toUnitSection U 1 := by
    apply ofUnitSection_injective
    rw [ofUnitSection_smul, ofUnitSection_toUnitSection, mul_one]
  rw [hm, Hom.app_smul, hone, smul_zero, Hom.zero_app]
  rfl

private theorem germToFunctionField_topIso {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (a : Γ((U : Scheme.{u}), ⊤)) :
    let _ : Nonempty (U.ι ''ᵁ ⊤) :=
      (Scheme.Opens.ι_image_top U).symm ▸ (inferInstance : Nonempty U)
    X.germToFunctionField U (U.topIso.hom a) = X.germToFunctionField (U.ι ''ᵁ ⊤) a := by
  let : Nonempty (U.ι ''ᵁ ⊤) :=
    (Scheme.Opens.ι_image_top U).symm ▸ (inferInstance : Nonempty U)
  rw [Scheme.Opens.topIso_hom]
  exact X.presheaf.germ_res_apply' _ _ _ a

/-- The actual meromorphic presentation of a line bundle constructs a nonzero
rational ratio, and every affine frame computes precisely this same function. -/
theorem exists_rationalSectionRatio
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F) {L : M.C.Modules} (hL : Scheme.Modules.IsInvertible L)
    (s t : 𝟙_ M.C.Modules ⟶ L) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ f : F, f ≠ 0 ∧
      ∀ (U : M.C.affineOpens) [Nonempty U.1]
        (τ : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        f = M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff s U.1 τ.hom)) /
          M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff t U.1 τ.hom)) := by
  obtain ⟨_D, φ, hnat, hsmul, hinj, _hrange, _horder⟩ :=
    hL.exists_divisor_range_eq_lSpaceOn M.toBase L
  have : Nonempty (⊤ : M.C.Opens) := ⟨⟨genericPoint M.C, trivial⟩⟩
  have hsφ : φ ⊤ (sectionValue s) ≠ 0 := by
    intro hz
    exact sectionValue_ne_zero s hs ((hinj ⊤ inferInstance)
      (hz.trans (map_zero (φ ⊤)).symm))
  have htφ : φ ⊤ (sectionValue t) ≠ 0 := by
    intro hz
    exact sectionValue_ne_zero t ht ((hinj ⊤ inferInstance)
      (hz.trans (map_zero (φ ⊤)).symm))
  refine ⟨M.ffEquiv.symm (φ ⊤ (sectionValue s) / φ ⊤ (sectionValue t)),
    fun hz => (div_ne_zero hsφ htφ)
      (M.ffEquiv.symm.injective (hz.trans (map_zero M.ffEquiv.symm).symm)), ?_⟩
  intro U hU τ
  let V : M.C.Opens := U.1.ι ''ᵁ ⊤
  have : Nonempty V := by
    change Nonempty (U.1.ι ''ᵁ ⊤)
    rw [Scheme.Opens.ι_image_top]
    exact hU
  let e : Γ(L, V) := τ.inv.app ⊤ (toUnitSection ⊤ 1)
  have he : e ≠ 0 := by
    intro hz
    have hz' : toUnitSection (X := (U.1 : Scheme.{u})) ⊤ 1 = 0 :=
      (ConcreteCategory.bijective_of_isIso (τ.inv.app ⊤)).1
        (hz.trans (τ.inv.app ⊤).hom.map_zero.symm)
    exact (one_ne_zero : (1 : Γ(M.C, V)) ≠ 0) hz'
  have heφ : φ V e ≠ 0 := fun hz => he ((hinj V inferInstance)
    (hz.trans (map_zero (φ V)).symm))
  have hcoord (q : 𝟙_ M.C.Modules ⟶ L) :
      φ ⊤ (sectionValue q) =
        M.C.germToFunctionField U.1 (coeff q U.1 τ.hom) * φ V e := by
    let a : Γ(M.C, V) := ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection q U.1))
    have hqa : a • e = restrictSection q U.1 :=
      ZeroSchemeLoc.coord_smul_gen τ ⊤ (restrictSection q U.1)
    have hres : L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (sectionValue q) =
        restrictSection q U.1 := sectionValue_res q V
    calc
      φ ⊤ (sectionValue q) = φ V (restrictSection q U.1) :=
        (hnat ⊤ V le_top inferInstance (sectionValue q)).symm.trans (congrArg (φ V) hres)
      _ = φ V (a • e) := congrArg (φ V) hqa.symm
      _ = M.C.germToFunctionField V a * φ V e := hsmul V a e
      _ = M.C.germToFunctionField U.1 (coeff q U.1 τ.hom) * φ V e :=
        congrArg (· * φ V e) (germToFunctionField_topIso U.1 a).symm
  rw [hcoord s, hcoord t, mul_div_mul_right _ _ heφ, map_div₀]

end AlgebraicCurve.CurveModel
