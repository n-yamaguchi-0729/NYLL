/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.LocalizationAtRootPrime
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerGaloisNormalization
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.RootCompletionBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.StandardCompletion
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import Nyll.SchemeTheory.LocalGeometry.HeightOne.Localization
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Prime-to-p Galois normalization at the actual root divisor

Let `t` be a prime parameter in a regular domain `R`. For a finite Galois
extension of the fraction field of `R_(t)` whose degree is prime to the
positive residue characteristic, adjoin the degree-th root of `t` on `R`
itself. The normalization at the actual root divisor is finite étale.

The comparison with the corresponding root extension of the DVR `R_(t)`,
the induced fraction-field comparison, and the identification of the two
normalizations are constructed from their actual maps. All components of
the generic tensor product are retained.

This supplies the boundary localization calculation used in Stacks Project
58.30.3, https://stacks.math.columbia.edu/tag/0C0R. Purity and gluing on a
smooth proper scheme are subsequent steps.
-/

noncomputable section

open Polynomial
open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uR uL

/-- The actual degree-th root chart has finite étale normalization at its
root divisor for a Galois extension of degree prime to the positive residue
characteristic. The local root and generic tensor comparisons are supplied
internally. -/
theorem finiteEtale_rootDivisorGaloisDegree_normalization
    (R : Type uR) [CommRing R] [IsDomain R] [IsRegularRing R]
    (t : R) (ht : Prime t) (L : Type uL) (p : ℕ) (hp : p.Prime) :
    let P := Ideal.span ({t} : Set R)
    let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime ht
    let V := Localization.AtPrime P
    let K := FractionRing V
    ∀ [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [CharP (V ⧸ IsLocalRing.maximalIdeal V) p],
      Nat.Coprime (Module.finrank K L) p →
      let n := Module.finrank K L
      let hn : 0 < n := Module.finrank_pos
      let D := AdjoinRoot (X ^ n - C t)
      let q := Ideal.span ({AdjoinRoot.root (X ^ n - C t)} : Set D)
      let : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
        (prime_adjoinRoot_root_of_prime hn ht)
      let : q.LiesOver P := span_root_liesOver_span_radicand hn ht
      let W := Localization.AtPrime q
      let : Algebra V W := Localization.AtPrime.algebraOfLiesOver P q
      let : IsDomain W := adjoinRootLocalizationAtRootPrime_isDomain hn ht
      let : IsDiscreteValuationRing W :=
        adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing hn ht
      let π := algebraMap R V t
      let Rn := AdjoinRoot (X ^ n - C π)
      let eLocal : Rn ≃ₐ[V] W := adjoinRootLocalizationAtRootPrimeAlgEquiv hn ht
      let : Module.Free V Rn := (monic_X_pow_sub_C π hn.ne').free_adjoinRoot
      let : Module.Free V W := Module.Free.of_equiv eLocal.toLinearEquiv
      let Kroot := FractionRing W
      let : Algebra K Kroot := FractionRing.liftAlgebra V Kroot
      let A := Kroot ⊗[K] L
      let : Algebra W A := genericTensorProductLeftScalarAlgebra
      Module.Finite W (integralClosure W A) ∧ Algebra.Etale W (integralClosure W A) := by
  intro P hP V K hFieldL aKL hFiniteL hGaloisL hCharV hdegree
    n hn D q hq hqP W aVW hDomainW hDvrW π Rn eLocal hFreeRn hFreeW Kroot aKKroot A aWA
  have : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtSpan_of_prime R t ht
  have hπne : π ≠ 0 := by
    intro hzero
    exact ht.ne_zero ((IsLocalization.injective V P.primeCompl_le_nonZeroDivisors)
      (hzero.trans (map_zero (algebraMap R V)).symm))
  have hπspan : IsLocalRing.maximalIdeal V = Ideal.span ({π} : Set V) :=
    localizationAtPrime_maximalIdeal_eq_span_of_eq_span P t rfl
  have hπ : Prime π :=
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπne hπspan).prime
  have : IsDomain Rn := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
  have : IsDiscreteValuationRing Rn :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
  have : Module.FaithfullyFlat V Rn := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
  let F := FractionRing Rn
  let : Algebra K F := FractionRing.liftAlgebra V F
  have : IsScalarTower V K F := FractionRing.isScalarTower_liftAlgebra V F
  have : IsScalarTower V K Kroot := FractionRing.isScalarTower_liftAlgebra V Kroot
  let B := F ⊗[K] L
  let : Algebra Rn B := genericTensorProductLeftScalarAlgebra
  have hEtaleB : Algebra.Etale Rn (integralClosure Rn B) :=
    (finiteEtale_uniformizerGaloisDegreeRoot_normalization V L p hp hdegree π hπ).2.2.2.2.1
  let eField : F ≃ₐ[K] Kroot :=
    IsFractionRing.fieldEquivOfAlgEquiv K F Kroot eLocal
  let eTensor : B ≃ₐ[K] A :=
    Algebra.TensorProduct.congr eField (AlgEquiv.refl : L ≃ₐ[K] L)
  have hmap (r : Rn) :
      eTensor (algebraMap Rn B r) = algebraMap W A (eLocal r) := by
    change eTensor (algebraMap Rn F r ⊗ₜ[K] 1) =
      algebraMap W Kroot (eLocal r) ⊗ₜ[K] 1
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    exact congrArg (fun x : Kroot ↦ x ⊗ₜ[K] (1 : L))
      (IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K F Kroot eLocal r)
  have hEtale : Algebra.Etale W (integralClosure W A) := by
    refine integralClosure_etale_of_baseAndAmbientEquiv
      eLocal.symm.toRingEquiv eTensor.symm.toRingEquiv ?_ hEtaleB
    ext w
    change eTensor.symm (algebraMap W A w) = algebraMap Rn B (eLocal.symm w)
    apply eTensor.injective
    rw [AlgEquiv.apply_symm_apply, hmap, AlgEquiv.apply_symm_apply]
  have : Algebra.FinitePresentation W (integralClosure W A) := hEtale.finitePresentation
  have hFiniteType : Algebra.FiniteType W (integralClosure W A) :=
    Algebra.FiniteType.of_finitePresentation (R := W) (A := integralClosure W A)
  exact ⟨Algebra.IsIntegral.finite (R := W) (A := integralClosure W A)
    (h' := hFiniteType), hEtale⟩

end EtaleFundamentalGroups.Kummer
