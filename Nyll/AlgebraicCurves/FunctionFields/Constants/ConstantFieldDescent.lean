/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_constantFieldDescent.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Basic.Complex.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantFieldDescentFinset
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveTranscendentalSeparable
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry

/-!
# Exists constant Field Descent
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Exists_constantFieldDescent
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open IntermediateField

universe u v

open AlgebraicCurve

namespace W4B

theorem essFiniteType_of_fg' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨x, -, hfin⟩ := hfg
  have h1 : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have h2 : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

theorem hasCanonicalDivisor_of_charZero' (K F : Type*) [Field K] [Field F] [Algebra K F]
    [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    HasCanonicalDivisor (K := K) (F := F) := by
  have : Algebra.EssFiniteType K F := essFiniteType_of_fg' hfg
  have : PerfectField K := PerfectField.ofCharZero
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K) (F := F)

end W4B

theorem _root_.AlgebraicCurve.exists_constantFieldDescent (K : Type u) (F : Type v) [Field K]
  [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀)
      (_ : IsCurveOver K₀ F₀) (_ : HasCanonicalDivisor (K := K₀) (F := F₀)),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  obtain ⟨x, hx, hfin⟩ := hfg
  obtain ⟨K₀, F₀, _, _, _, _, _, _, _, _, algC, _, _, _, ⟨x₀, hx₀, hfin₀⟩, htop, _⟩ :=
    AlgebraicCurves.FunctionFields.Proofs.Exists_constantFieldDescent_finset.W7XDesc.core
      K F hx hfin ∅
  have : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap K₀ F₀).injective
  have : Algebra.IsSeparable (IntermediateField.adjoin K₀ ({x₀} : Set F₀)) F₀ := inferInstance
  have hC : IsCurveOver K₀ F₀ :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K₀ F₀ x₀ hx₀ hfin₀ inferInstance
  have hK : HasCanonicalDivisor (K := K₀) (F := F₀) :=
    W4B.hasCanonicalDivisor_of_charZero' K₀ F₀ ⟨x₀, hx₀, hfin₀⟩
  exact ⟨K₀, F₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, algC, inferInstance, inferInstance, hC, hK,
    ⟨x₀, hx₀, hfin₀⟩, htop⟩
end AlgebraicCurves.FunctionFields.Proofs.Exists_constantFieldDescent
end ProofImplementation
