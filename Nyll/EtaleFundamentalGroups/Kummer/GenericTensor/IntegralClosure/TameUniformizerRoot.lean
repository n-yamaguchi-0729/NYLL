/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Henselian.PrimeToUniformizerRadical
import Nyll.EtaleFundamentalGroups.Kummer.Henselian.UniformizerDecomposition
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.ActualCompositum.TensorComponent
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.FixedTensor.IntrinsicCoordinates
import Nyll.EtaleFundamentalGroups.Kummer.PureRadical.GenericTensorComponent
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalTame
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless
import Mathlib.Algebra.CharP.Invertible

/-!
# Literal tensor components after a tame uniformizer root

For a finite extension of DVR valuation rings, a separable residue
extension and an invertible ramification index give an étale
normalization of every literal generic tensor component after a
divisible root of the base uniformizer. The target uniformizer, its
unit decomposition, and the root in the algebraic closure are produced
from the chosen component.

For degree prime to the positive residue characteristic, the finite-ring
degree identity supplies both tame conditions and divisibility of the
ramification index by the field degree. Thus the degree itself can be
used as the root exponent. This is the tensor-component form of the
local tame calculation in Stacks Project 58.30.3:
https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uL uW uF

/-- The actual normalization of each fixed generic tensor component is
étale after a root divisible by the tame ramification index. -/
theorem integralClosure_uniformizerTensorComponent_etale_of_tame
    {K : Type uK} {L : Type uL} {F : Type uF}
    [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable base.residueField target.residueField]
    (heUnit : IsUnit (ramificationIndex base target : base.valuationSubring))
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) (hdiv : ramificationIndex base target ∣ N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let P := GenericTensorFieldComponent m
    let : Algebra Rn P := pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
    Algebra.Etale Rn (integralClosure Rn P) := by
  intro Rn P aRP
  have hvarpiPrime : Prime varpi := dvfUniformizer_prime base varpi hvarpi
  have : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  have : IsFractionRing base.valuationSubring K := base.valuationSubring_isFractionRing
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let rootP := pureRadicalFractionFieldGenericTensorComponentRoot (N := N) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding hN varpi hvarpiPrime m
  let gamma := j rootP
  have hgamma : gamma ^ N = algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow base hN varpi hvarpiPrime m
  obtain ⟨pi, hpi⟩ := target.exists_uniformizer
  obtain ⟨unit, hdecomp⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
      base target hvarpi hpi
  obtain ⟨factor⟩ := higherRadicalActualFactorData_of_tame base target heUnit
    varpi hvarpi pi unit hpi hdecomp N hN hdiv gamma hgamma
  exact integralClosure_tensorComponent_etale_of_higherRadicalActualFactorData
    base target hN varpi hvarpiPrime m factor

/-- Degree prime to the positive residue characteristic supplies the tame
conditions internally. Any positive multiple of that degree removes the
ramification in every fixed generic tensor component. -/
theorem integralClosure_uniformizerTensorComponent_etale_of_degree_coprime
    {K : Type uK} {L : Type uL} {F : Type uF}
    [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    [FiniteDimensional K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (p : ℕ) (hp : p.Prime) [CharP base.residueField p]
    (hdegree : Nat.Coprime (Module.finrank K L) p)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) (hdiv : Module.finrank K L ∣ N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let P := GenericTensorFieldComponent m
    let : Algebra Rn P := pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
    Algebra.Etale Rn (integralClosure Rn P) := by
  intro Rn P aRP
  have hIndexDegree : ramificationIndex base target ∣ Module.finrank K L := by
    have h := isDefectless_of_moduleFinite base target
    rw [IsDefectless, degree_eq_finrank] at h
    exact ⟨residueDegree base target, h⟩
  have heCoprime : Nat.Coprime (ramificationIndex base target) p :=
    hdegree.of_dvd_left hIndexDegree
  have heResidueUnit : IsUnit (ramificationIndex base target : base.residueField) :=
    (CharP.isUnit_natCast_iff hp).mpr (hp.coprime_iff_not_dvd.mp heCoprime.symm)
  have heUnit : IsUnit (ramificationIndex base target : base.valuationSubring) := by
    apply (base.residue_ne_zero_iff_isUnit _).mp
    rw [map_natCast]
    exact heResidueUnit.ne_zero
  have : Algebra.IsSeparable base.residueField target.residueField :=
    residue_isSeparable_of_moduleFinite_of_degree_coprime base target p hp hdegree
  exact integralClosure_uniformizerTensorComponent_etale_of_tame base target heUnit
    varpi hvarpi N hN (hIndexDegree.trans hdiv) m

end EtaleFundamentalGroups.Kummer
