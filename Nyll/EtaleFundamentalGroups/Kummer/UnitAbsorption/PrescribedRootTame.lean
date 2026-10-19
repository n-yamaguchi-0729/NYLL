/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.Compositum
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.PureRadicalTame
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Basic

/-!
# A finite étale model for a prescribed tame uniformizer root

For a finite extension of DVRs with separable residue extension and
invertible ramification index `e`, a prescribed root `alpha` of the base
uniformizer produces the actual unit root `delta = alpha / pi`.
Its integral minimal polynomial gives a finite étale algebra over the
target DVR. The concrete map from the pure uniformizer radical is
constructed by sending its root to `root(q) * pi`.

The same algebra is finite étale over that pure radical, and its generic
field is the actual compositum of the target field with `K(alpha)`.
Both root coordinates are retained. These are the tame local models used
in Stacks Project, Proposition 58.30.3:
https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

/-- A prescribed tame uniformizer root has a concrete finite étale unit
factor over both DVRs, with its original compositum and both generators. -/
theorem exists_finiteEtale_unitFactor_for_prescribed_tame_uniformizerRoot
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable base.residueField target.residueField]
    (heUnit : IsUnit (ramificationIndex base target : base.valuationSubring))
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (pi : target.valuationSubring) (unit : target.valuationSubringˣ)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hdecomp : integerMap base target varpi =
      (unit : target.valuationSubring) * pi ^ ramificationIndex base target)
    (alpha : AlgebraicClosure L)
    (halphaPow : alpha ^ ramificationIndex base target =
      algebraMap K (AlgebraicClosure L) (varpi : K)) :
    let e := ramificationIndex base target
    ∃ (delta : AlgebraicClosure L) (q : target.valuationSubring[X])
      (unitFactorEquiv :
        AdjoinRoot (q.map (algebraMap target.valuationSubring L)) ≃ₐ[L]
          IntermediateField.adjoin L ({delta} : Set (AlgebraicClosure L)))
      (radicalToUnitFactor :
        AdjoinRoot (X ^ e - C varpi) →ₐ[base.valuationSubring] AdjoinRoot q),
      delta ^ e = algebraMap L (AlgebraicClosure L) (unit : L) ∧
      alpha = delta * algebraMap L (AlgebraicClosure L) (pi : L) ∧
      q.Monic ∧ q.map (algebraMap target.valuationSubring L) = minpoly L delta ∧
      q ∣ X ^ e - C (unit : target.valuationSubring) ∧
      Module.Finite target.valuationSubring (AdjoinRoot q) ∧
      Algebra.Etale target.valuationSubring (AdjoinRoot q) ∧
      (IntermediateField.adjoin L ({delta} : Set (AlgebraicClosure L))).restrictScalars K =
        (IsScalarTower.toAlgHom K L (AlgebraicClosure L)).fieldRange ⊔
          IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L)) ∧
      unitFactorEquiv (AdjoinRoot.root (q.map (algebraMap target.valuationSubring L))) =
        IntermediateField.AdjoinSimple.gen L delta ∧
      radicalToUnitFactor (AdjoinRoot.root (X ^ e - C varpi)) =
        AdjoinRoot.root q * algebraMap target.valuationSubring (AdjoinRoot q) pi ∧
      (let : Algebra (AdjoinRoot (X ^ e - C varpi)) (AdjoinRoot q) :=
          radicalToUnitFactor.toRingHom.toAlgebra
       Module.Finite (AdjoinRoot (X ^ e - C varpi)) (AdjoinRoot q) ∧
         Algebra.Etale (AdjoinRoot (X ^ e - C varpi)) (AdjoinRoot q)) := by
  intro e
  let V := base.valuationSubring
  let W := target.valuationSubring
  have he : 0 < e := by
    apply Nat.pos_of_ne_zero
    simpa only [e, ramificationIndex] using
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
        (maximalIdeal_map_integerMap_ne_bot base target)
        (IsLocalRing.maximalIdeal.isMaximal W).isPrime
        (maximalIdeal_map_integerMap_le base target))
  have heW : IsUnit (e : W) := by
    simpa only [map_natCast] using heUnit.map (integerMap base target)
  have hdecompL : algebraMap K L (varpi : K) = (unit : L) * (pi : L) ^ e :=
    congrArg (fun z : W ↦ (z : L)) hdecomp
  let beta := algebraMap L (AlgebraicClosure L) (pi : L)
  have hbeta : beta ≠ 0 := by
    simpa only [beta, map_zero] using
      (algebraMap L (AlgebraicClosure L)).injective.ne hpi.ne_zero
  let delta := alpha / beta
  have hdelta : delta ^ e = algebraMap L (AlgebraicClosure L) (unit : L) := by
    change (alpha / beta) ^ e = algebraMap L (AlgebraicClosure L) (unit : L)
    rw [div_pow, halphaPow, IsScalarTower.algebraMap_apply K L (AlgebraicClosure L),
      hdecompL, map_mul, map_pow]
    exact mul_div_cancel_right₀ _ (pow_ne_zero e hbeta)
  have halpha : alpha = delta * beta := (div_mul_cancel₀ alpha hbeta).symm
  have : IsFractionRing W L := target.valuationSubring_isFractionRing
  have : IsIntegrallyClosed W := target.valuationSubring_isIntegrallyClosed
  obtain ⟨q, unitFactorEquiv, hqMonic, hqMap, hqDvd, hqEtale, hqFinite, hFactorRoot⟩ :=
    exists_finiteEtale_integralFactor_of_pow_eq_unit
      (B := W) (L := L) (Omega := AlgebraicClosure L) he heW unit delta hdelta
  let T := AdjoinRoot q
  let d : T := AdjoinRoot.root q
  have hqRoot : aeval d q = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hdPow : d ^ e = algebraMap W T (unit : W) := by
    apply sub_eq_zero.mp
    have hroot : aeval d (X ^ e - C (unit : W)) = 0 := by
      obtain ⟨r, hr⟩ := hqDvd
      rw [hr, map_mul, hqRoot, zero_mul]
    simpa only [map_sub, map_pow, aeval_X, aeval_C] using hroot
  let rootInFactor : T := d * algebraMap W T pi
  have hrootPow : rootInFactor ^ e = algebraMap V T varpi := by
    calc
      rootInFactor ^ e = d ^ e * (algebraMap W T pi) ^ e := mul_pow _ _ e
      _ = algebraMap W T ((unit : W) * pi ^ e) := by
        rw [hdPow, map_mul, map_pow]
      _ = algebraMap W T (integerMap base target varpi) :=
        congrArg (algebraMap W T) hdecomp.symm
      _ = algebraMap V T varpi := (IsScalarTower.algebraMap_apply V W T varpi).symm
  have hrootPoly : aeval rootInFactor (X ^ e - C varpi) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hrootPow, sub_self]
  let radicalToUnitFactor : AdjoinRoot (X ^ e - C varpi) →ₐ[V] T :=
    AdjoinRoot.liftAlgHom (X ^ e - C varpi) (Algebra.ofId V T) rootInFactor hrootPoly
  have hRadicalRoot : radicalToUnitFactor (AdjoinRoot.root (X ^ e - C varpi)) =
      AdjoinRoot.root q * algebraMap W T pi :=
    AdjoinRoot.liftAlgHom_root (X ^ e - C varpi) (Algebra.ofId V T)
      rootInFactor hrootPoly
  have hCompositum := restrictScalars_adjoin_eq_fieldRange_sup_adjoin_of_eq_mul
    (K := K) (L := L) delta alpha (pi : L) halpha hpi.ne_zero
  have hRootFiniteEtale :
      let : Algebra (AdjoinRoot (X ^ e - C varpi)) T :=
        radicalToUnitFactor.toRingHom.toAlgebra
      Module.Finite (AdjoinRoot (X ^ e - C varpi)) T ∧
        Algebra.Etale (AdjoinRoot (X ^ e - C varpi)) T := by
    intro aRT
    let R := AdjoinRoot (X ^ e - C varpi)
    have : Module.Finite W T := hqFinite
    have : Module.Finite V T := Module.Finite.trans W T
    have : IsScalarTower V R T :=
      IsScalarTower.of_algebraMap_eq fun r ↦ (radicalToUnitFactor.commutes r).symm
    exact ⟨Module.Finite.of_restrictScalars_finite V R T,
      unitFactor_etale_over_uniformizerRadical_of_residue_isSeparable
        base target varpi hvarpi delta q hqMonic hqMap hqEtale radicalToUnitFactor⟩
  exact ⟨delta, q, unitFactorEquiv, radicalToUnitFactor, hdelta, halpha,
    hqMonic, hqMap, hqDvd, hqFinite, hqEtale, hCompositum, hFactorRoot,
    hRadicalRoot, hRootFiniteEtale⟩

end EtaleFundamentalGroups.Kummer
