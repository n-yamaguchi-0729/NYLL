/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerRamification
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Purity.Local.DimensionOne
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.ResidueSeparableTower
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Flat

/-!
# Unit absorption with a separable residue extension

The finite étale unit factor in a finite extension of DVRs is also étale
over the ramification-index root of the base uniformizer when the actual
residue extension is separable. No perfectness or characteristic-zero
hypothesis is imposed on the residue field.

The root algebra's DVR structure and ramification index are supplied by
the existing uniformizer-root calculation. Two ramification towers show
that every maximal prime of the unit factor has index one over the root
algebra. The residue extension remains separable along the étale tower,
and separability passes to the intermediate root algebra. Flatness then
gives étaleness.

This is the local tame unit-absorption step needed for Stacks Project,
Proposition 58.30.3: https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

private theorem etale_of_equal_closed_ramification
    (V : Type u) (W : Type v) (R : Type w) (T : Type x)
    [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing T]
    [Algebra V W] [Algebra V R] [Algebra W T] [Algebra R T] [Algebra V T]
    [IsScalarTower V W T] [IsScalarTower V R T]
    [Module.Finite V W] [Module.Finite W T] [Module.IsTorsionFree R T]
    [Algebra.Etale W T]
    [Algebra.HasSeparableResidueFieldsAt V T (IsLocalRing.maximalIdeal V)]
    (hindex : (IsLocalRing.maximalIdeal R).ramificationIdx V =
      (IsLocalRing.maximalIdeal W).ramificationIdx V)
    (hpos : 0 < (IsLocalRing.maximalIdeal W).ramificationIdx V) :
    Algebra.Etale R T := by
  have : Module.Finite V T := Module.Finite.trans W T
  have : Module.Finite R T := Module.Finite.of_restrictScalars_finite V R T
  have : Module.Flat R T := inferInstance
  apply etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
  intro P hPmax
  have : P.IsPrime := hPmax.isPrime
  have hPW : P.under W = IsLocalRing.maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)
  have hPR : P.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)
  have hPV : P.under V = IsLocalRing.maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)
  have hleft := Ideal.ramificationIdx_tower (R := V) (P.under W) P
  rw [Ideal.ramificationIdx_eq_one P W, mul_one, hPW] at hleft
  have hright := Ideal.ramificationIdx_tower (R := V) (P.under R) P
  have hPindex : P.ramificationIdx R = 1 := by
    rw [hPR, hindex, hleft] at hright
    apply Nat.eq_of_mul_eq_mul_left hpos
    simpa only [mul_one] using hright.symm
  have : (P.under R).LiesOver (IsLocalRing.maximalIdeal V) :=
    ⟨by rw [Ideal.under_under, hPV]⟩
  have : Algebra.HasSeparableResidueFieldsAt R T (P.under R) :=
    Algebra.HasSeparableResidueFieldsAt.tower_top
      (A := V) (B := R) (C := T) (IsLocalRing.maximalIdeal V) (P.under R)
  exact (Ideal.ramificationIdx_eq_one_iff (q := P) (R := R)).mp hPindex

/-- With a separable residue extension, the actual finite étale unit factor
is étale over the pure uniformizer radical in arbitrary characteristic.
The radical map is the concrete algebra map supplied by unit absorption;
its étaleness is proved from the two ramification towers. -/
theorem unitFactor_etale_over_uniformizerRadical_of_residue_isSeparable
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable base.residueField target.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (delta : AlgebraicClosure L)
    (q : target.valuationSubring[X])
    (hqMonic : q.Monic)
    (hqMap : q.map (algebraMap target.valuationSubring L) = minpoly L delta)
    (hqEtale : Algebra.Etale target.valuationSubring (AdjoinRoot q))
    (radicalToUnitFactor :
      AdjoinRoot (X ^ ramificationIndex base target - C varpi) →ₐ[base.valuationSubring]
        AdjoinRoot q) :
    let : Algebra (AdjoinRoot (X ^ ramificationIndex base target - C varpi))
        (AdjoinRoot q) := radicalToUnitFactor.toRingHom.toAlgebra
    Algebra.Etale (AdjoinRoot (X ^ ramificationIndex base target - C varpi))
      (AdjoinRoot q) := by
  intro aRT
  let V := base.valuationSubring
  let W := target.valuationSubring
  let e := ramificationIndex base target
  let R := AdjoinRoot (X ^ e - C varpi)
  let T := AdjoinRoot q
  have : IsDiscreteValuationRing V := base.valuationSubring_isDiscreteValuationRing
  have : IsDiscreteValuationRing W := target.valuationSubring_isDiscreteValuationRing
  have : IsFractionRing W L := target.valuationSubring_isFractionRing
  have he : 0 < e := by
    apply Nat.pos_of_ne_zero
    simpa only [e, ramificationIndex] using
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
        (maximalIdeal_map_integerMap_ne_bot base target)
        (IsLocalRing.maximalIdeal.isMaximal W).isPrime
        (maximalIdeal_map_integerMap_le base target))
  have hvarpiPrime : Prime varpi := by
    have hne : varpi ≠ 0 := fun hz ↦ hvarpi.ne_zero (congrArg Subtype.val hz)
    apply (Ideal.span_singleton_prime hne).mp
    rw [← Valuation.IsUniformizer.is_generator hvarpi]
    exact (IsLocalRing.maximalIdeal.isMaximal V).isPrime
  have : IsDomain R := isDomain_adjoinRoot_X_pow_sub_C_of_prime he varpi hvarpiPrime
  have : IsDiscreteValuationRing R :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime he varpi hvarpiPrime
  have : Module.Finite V R := (monic_X_pow_sub_C varpi he.ne').finite_adjoinRoot
  have hqIrreducible : Irreducible q := by
    apply (hqMonic.irreducible_iff_irreducible_map_fraction_map (K := L)).mpr
    rw [hqMap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral delta)
  have : IsDomain T := AdjoinRoot.isDomain_of_prime hqIrreducible.prime
  have : Module.Finite W T := hqMonic.finite_adjoinRoot
  have : Algebra.Etale W T := hqEtale
  have : IsScalarTower V R T :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (radicalToUnitFactor.commutes z).symm
  have hVTinjective : Function.Injective (algebraMap V T) := by
    rw [IsScalarTower.algebraMap_eq V W T]
    have hqDegree : q.degree ≠ 0 := by
      rw [← degree_map_eq_of_injective (IsFractionRing.injective W L) q, hqMap]
      exact (minpoly.degree_pos (Algebra.IsIntegral.isIntegral delta)).ne'
    exact (AdjoinRoot.of.injective_of_degree_ne_zero hqDegree).comp
      (integerMap_injective base target)
  have hRTinjective : Function.Injective (algebraMap R T) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_under_eq_bot (R := V)
    rw [Ideal.under, RingHom.comap_ker]
    have hcomp : (algebraMap R T).comp (algebraMap V R) = algebraMap V T :=
      (IsScalarTower.algebraMap_eq V R T).symm
    rw [hcomp, (RingHom.injective_iff_ker_eq_bot _).mp hVTinjective]
  have : Module.IsTorsionFree R T :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hRTinjective
  have : Module.IsTorsionFree V W :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (integerMap_injective base target)
  have hramR : (IsLocalRing.maximalIdeal R).ramificationIdx V = e :=
    ramificationIdx_adjoinRoot_uniformizer he varpi hvarpiPrime
  have hramW : (IsLocalRing.maximalIdeal W).ramificationIdx V = e := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx
      (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) base.maximalIdeal_ne_bot]
    rfl
  have : Algebra.HasSeparableResidueFieldsAt V W (IsLocalRing.maximalIdeal V) :=
    SchemeTheory.hasSeparableResidueFieldsAt_maximalIdeal_of_isLocalRing V W
  have : Algebra.HasSeparableResidueFieldsAt V T (IsLocalRing.maximalIdeal V) :=
    SchemeTheory.hasSeparableResidueFieldsAt_of_etale_tower V W T
      (IsLocalRing.maximalIdeal V)
  exact etale_of_equal_closed_ramification V W R T (hramR.trans hramW.symm)
    (hramW.symm ▸ he)

end EtaleFundamentalGroups.Kummer
