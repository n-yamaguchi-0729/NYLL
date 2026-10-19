/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Henselian.UniformizerDecomposition
import Nyll.EtaleFundamentalGroups.Kummer.Henselian.UnitRoot
import Nyll.EtaleFundamentalGroups.Kummer.Obstructions.LocalDerivative
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless
import Mathlib.Algebra.CharP.Invertible
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# A uniformizer radical in prime to residue characteristic degree

For a finite extension of DVR valuation rings, the degree identity
`[L : K] = e f` implies that the inseparable residue degree divides the
field degree. A degree prime to the positive residue characteristic
therefore forces the actual residue extension to be separable.

If both valued fields are henselian and the base residue field is
separably closed, the residue extension is then trivial. Hensel's lemma
absorbs the unit in a uniformizer comparison. The resulting root has an
Eisenstein minimal polynomial of degree `[L : K]`, so it generates `L`.

No Galois assumption is needed for this local result. Finiteness of the
target valuation ring is essential to the degree identity used here.
This supplies the positive characteristic radical calculation for
Stacks Project, Proposition 58.30.3:
https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

/-- A finite extension of DVR valuation rings of degree prime to the
positive residue characteristic has separable residue extension. The
inseparable degree is ruled out by the actual finite-ring degree identity. -/
theorem residue_isSeparable_of_moduleFinite_of_degree_coprime
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (p : ℕ) (hp : p.Prime) [CharP base.residueField p]
    (hdegree : Nat.Coprime (Module.finrank K L) p) :
    Algebra.IsSeparable base.residueField target.residueField := by
  have : target.maximalIdeal.LiesOver base.maximalIdeal :=
    ⟨(maximalIdeal_comap_integerMap_eq base target).symm⟩
  have : FiniteDimensional base.residueField target.residueField := by
    apply FiniteDimensional.of_finrank_pos
    have h := Ideal.inertiaDeg_pos target.maximalIdeal base.valuationSubring
    rw [Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal] at h
    exact h
  have hformula : Module.finrank K L = ramificationIndex base target *
      Module.finrank base.residueField target.residueField := by
    have h := isDefectless_of_moduleFinite base target
    rw [IsDefectless, degree_eq_finrank, residueDegree,
      Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal] at h
    exact h
  have hInsepResidue : Field.finInsepDegree base.residueField target.residueField ∣
      Module.finrank base.residueField target.residueField := by
    rw [← Field.finSepDegree_mul_finInsepDegree]
    exact dvd_mul_left _ _
  have hInsepDegree : Field.finInsepDegree base.residueField target.residueField ∣
      Module.finrank K L := hInsepResidue.trans (by
    rw [hformula]
    exact dvd_mul_left _ _)
  have : ExpChar base.residueField p := ExpChar.prime hp
  obtain ⟨m, hm⟩ := finInsepDegree_eq_pow base.residueField target.residueField p
  have hmzero : m = 0 := by
    by_contra hne
    have hpd : p ∣ Module.finrank K L := by
      apply dvd_trans _ hInsepDegree
      rw [hm]
      exact dvd_pow_self p hne
    exact (hp.coprime_iff_not_dvd.mp hdegree.symm) hpd
  rw [isSeparable_iff_finInsepDegree_eq_one, hm, hmzero, pow_zero]

private theorem exists_uniformizer_radical_generator_of_residue_separable
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsSepClosed base.residueField]
    [Algebra.IsSeparable base.residueField target.residueField]
    (hunit : IsUnit (Module.finrank K L : base.residueField)) :
    ∃ (ϖ : base.valuationSubring) (α : L)
        (e : AdjoinRoot (X ^ Module.finrank K L - C (ϖ : K)) ≃ₐ[K] L),
      base.valuation.IsUniformizer (ϖ : K) ∧ Prime ϖ ∧
        α ^ Module.finrank K L = algebraMap K L (ϖ : K) ∧
        IntermediateField.adjoin K ({α} : Set L) = ⊤ ∧
        e (AdjoinRoot.root (X ^ Module.finrank K L - C (ϖ : K))) = α := by
  let n := Module.finrank K L
  have hn : 0 < n := Module.finrank_pos
  have : target.maximalIdeal.LiesOver base.maximalIdeal :=
    ⟨(maximalIdeal_comap_integerMap_eq base.toDVF target.toDVF).symm⟩
  have : FiniteDimensional base.residueField target.residueField := by
    apply FiniteDimensional.of_finrank_pos
    have h := Ideal.inertiaDeg_pos target.maximalIdeal base.valuationSubring
    rw [Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal] at h
    exact h
  have hresidue : Module.finrank base.residueField target.residueField = 1 :=
    Module.finrank_of_bijective_algebraMap
      (IsSepClosed.algebraMap_bijective base.residueField target.residueField)
  have hindex : ramificationIndex base.toDVF target.toDVF = n := by
    have hformula : n = ramificationIndex base.toDVF target.toDVF *
        Module.finrank base.residueField target.residueField := by
      have h := isDefectless_of_moduleFinite base.toDVF target.toDVF
      rw [IsDefectless, degree_eq_finrank, residueDegree,
        Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal] at h
      exact h
    rw [hresidue, mul_one] at hformula
    exact hformula.symm
  have : IsSepClosed target.residueField :=
    Algebra.IsAlgebraic.isSepClosed (F := base.residueField) (E := target.residueField)
  have hunitTarget : IsUnit (n : target.residueField) := by
    simpa only [map_natCast] using hunit.map (residueMap base.toDVF target.toDVF)
  obtain ⟨ϖ, π, u, hϖ, _hπ, hdecomp⟩ :=
    exists_uniformizers_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
      base.toDVF target.toDVF
  rw [hindex] at hdecomp
  obtain ⟨δ, hδ⟩ := exists_pow_eq_of_isUnit_of_isSepClosed_residue
    hunitTarget (u : target.valuationSubring) u.isUnit
  let αS : target.valuationSubring := δ * π
  let α : L := (αS : L)
  have hαS : αS ^ n = integerMap base.toDVF target.toDVF ϖ := by
    calc
      αS ^ n = δ ^ n * π ^ n := mul_pow δ π n
      _ = (u : target.valuationSubring) * π ^ n := by rw [hδ]
      _ = integerMap base.toDVF target.toDVF ϖ := hdecomp.symm
  have hαpow : α ^ n = algebraMap K L (ϖ : K) := by
    change ((αS ^ n : target.valuationSubring) : L) = algebraMap K L (ϖ : K)
    rw [hαS]
    exact integerMap_apply base.toDVF target.toDVF ϖ
  have hϖne : ϖ ≠ 0 := by
    intro hzero
    exact hϖ.ne_zero (congrArg Subtype.val hzero)
  have hϖprime : Prime ϖ := by
    apply (Ideal.span_singleton_prime hϖne).mp
    exact (base.toDVF.maximalIdeal_eq_span_uniformizer hϖ) ▸
      (IsLocalRing.maximalIdeal.isMaximal base.valuationSubring).isPrime
  let f : K[X] := X ^ n - C (ϖ : K)
  have hfIrreducible : Irreducible f :=
    irreducible_X_pow_sub_C_fractionRing_of_prime
      (R := base.valuationSubring) (K := K) hϖprime hn
  have hfMonic : f.Monic := monic_X_pow_sub_C (ϖ : K) hn.ne'
  have hfRoot : Polynomial.aeval α f = 0 := by
    change Polynomial.aeval α (X ^ n - C (ϖ : K)) = 0
    rw [map_sub, map_pow, aeval_X, aeval_C, hαpow, sub_self]
  have hfMinpoly : f = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hfIrreducible hfRoot hfMonic
  have hαIntegral : IsIntegral K α := IsIntegral.of_finite K α
  have hadjoinRank : Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = n := by
    rw [IntermediateField.adjoin.finrank hαIntegral, ← hfMinpoly]
    exact natDegree_X_pow_sub_C
  have hadjoin : IntermediateField.adjoin K ({α} : Set L) = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    simpa only [IntermediateField.finrank_top'] using hadjoinRank
  let e : AdjoinRoot f ≃ₐ[K] L :=
    (AdjoinRoot.algEquivOfEq K f (minpoly K α) hfMinpoly).trans
      ((IntermediateField.adjoinRootEquivAdjoin K hαIntegral).trans
        ((IntermediateField.equivOfEq hadjoin).trans IntermediateField.topEquiv))
  have heRoot : e (AdjoinRoot.root f) = α := by
    simp only [e, AlgEquiv.trans_apply, AdjoinRoot.algEquivOfEq_root,
      IntermediateField.adjoinRootEquivAdjoin_apply_root,
      IntermediateField.equivOfEq_apply]
    rfl
  exact ⟨ϖ, α, e, hϖ, hϖprime, hαpow, hadjoin, heRoot⟩

/-- A finite extension of henselian DVR valuation rings of degree prime
to the positive residue characteristic, with separably closed base residue
field, is generated by a root of a base uniformizer of that same degree. -/
theorem exists_uniformizer_radical_generator_of_moduleFinite_of_degree_coprime
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsSepClosed base.residueField]
    (p : ℕ) (hp : p.Prime) [CharP base.residueField p]
    (hdegree : Nat.Coprime (Module.finrank K L) p) :
    ∃ (ϖ : base.valuationSubring) (α : L)
        (e : AdjoinRoot (X ^ Module.finrank K L - C (ϖ : K)) ≃ₐ[K] L),
      base.valuation.IsUniformizer (ϖ : K) ∧ Prime ϖ ∧
        α ^ Module.finrank K L = algebraMap K L (ϖ : K) ∧
        IntermediateField.adjoin K ({α} : Set L) = ⊤ ∧
        e (AdjoinRoot.root (X ^ Module.finrank K L - C (ϖ : K))) = α := by
  have : Algebra.IsSeparable base.residueField target.residueField :=
    residue_isSeparable_of_moduleFinite_of_degree_coprime
      base.toDVF target.toDVF p hp hdegree
  have hunit : IsUnit (Module.finrank K L : base.residueField) :=
    (CharP.isUnit_natCast_iff hp).mpr (hp.coprime_iff_not_dvd.mp hdegree.symm)
  exact exists_uniformizer_radical_generator_of_residue_separable base target hunit

end EtaleFundamentalGroups.Kummer
