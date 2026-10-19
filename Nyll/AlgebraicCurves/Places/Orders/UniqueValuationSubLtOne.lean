/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Places.Orders.EqValuationSubLtOne

/-!
# Place exists Unique valuation sub lt one of constant Field Extension
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension

open Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.AlgebraicCurve
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace PointPlaceDictionary
open _root_.AlgebraicCurve

variable {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE]

theorem exists_centre_of_forall_mem [IsAlgClosed E] [IsCurveOver E FE] (P : Place E FE)
    (hP : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) :
    ∃ e : F →ₐ[K] E, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
  classical
  have : Module.Finite E P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral E P.ResidueField := Algebra.IsIntegral.of_finite E P.ResidueField
  have hbij : Function.Bijective (algebraMap E P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ρ : E ≃+* P.ResidueField := RingEquiv.ofBijective (algebraMap E P.ResidueField) hbij
  let ι : F →+* P.toValuationSubring := (algebraMap F FE).codRestrict P.toValuationSubring hP
  let r : F →+* P.ResidueField := (IsLocalRing.residue P.toValuationSubring).comp ι
  have hρ : ∀ c : E, ρ c = IsLocalRing.residue _ (algebraMap E P.toValuationSubring c) :=
    fun c => rfl
  have hr : ∀ a : K, r (algebraMap K F a) = ρ (algebraMap K E a) := by
    intro a
    rw [hρ]
    change IsLocalRing.residue _ (ι (algebraMap K F a)) = _
    congr 1
    apply Subtype.ext
    change algebraMap F FE (algebraMap K F a) = (algebraMap E P.toValuationSubring _ : FE)
    rw [Place.coe_algebraMap, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let e : F →ₐ[K] E :=
    { ρ.symm.toRingHom.comp r with
      commutes' := fun a => by
        change ρ.symm (r (algebraMap K F a)) = algebraMap K E a
        rw [hr, RingEquiv.symm_apply_apply] }
  refine ⟨e, fun f => ?_⟩
  have he : ρ (e f) = r f := by
    change ρ (ρ.symm (r f)) = r f
    exact ρ.apply_symm_apply _
  have hmem : (⟨algebraMap F FE f, hP f⟩ - algebraMap E P.toValuationSubring (e f) :
      P.toValuationSubring) ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hρ, he, sub_eq_zero]
    rfl
  have := (ValuationSubring.valuation_lt_one_iff _ _).mp hmem
  simpa [Place.coe_algebraMap] using this

end AlgebraicCurve.PointPlaceDictionary

open AlgebraicCurve.PointPlaceDictionary in
theorem _root_.AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    (∀ e : F →ₐ[K] E, ∃! P : Place E FE, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) ∧
    (∀ P : Place E FE, (∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) →
      ∃ e : F →ₐ[K] E, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) := by
  refine ⟨fun e => ?_, fun P hP => exists_centre_of_forall_mem P hP⟩
  obtain ⟨P, hP⟩ :=
    CentredPlaceRigidity.exists_centred
      hfg hfgE hgen e
  exact ⟨P, hP, fun Q hQ =>
    Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension K F hfg E FE hfgE hgen e
      Q P hQ hP⟩
end AlgebraicCurves.Places.Proofs.Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
end ProofImplementation
