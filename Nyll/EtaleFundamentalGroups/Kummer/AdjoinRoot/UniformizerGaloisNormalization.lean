/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.Completion
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.CompletionAdic
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerCompletion
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerCompletionTower
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerNormalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.ComponentPrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.Completions.RootTensor.GaloisPrimeTo
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.Refinement.NormalizationLocal
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.RootCompletionBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.NormalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRFiniteEtaleAlgebra
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Invertible
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Prime-to-p Galois normalization over an arbitrary DVR

For a finite Galois extension of the fraction field with degree prime to
the positive residue characteristic, adjoining a uniformizer root of that
degree removes ramification in the entire generic tensor product. The root
extension is itself finite separable of precisely that degree.

The proof passes to the actual standard completion, applies the complete
tame tensor theorem at every refined component, and descends étaleness by
faithful flatness. Neither completeness nor Henselianity is assumed of the
original DVR. The normalization and its generic-fibre identification are
constructed from the original extension.

This is the local normalized base-change calculation in Stacks Project
58.30.3, https://stacks.math.columbia.edu/tag/0C0R. Passing from these local
normalizations to a global smooth proper cover is a separate step.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct

universe uV uL

/-- A positive multiple of the prime-to-p Galois degree removes ramification
in each literal generic tensor component over an arbitrary root DVR. -/
theorem integralClosure_uniformizerRootTensorComponent_etale_of_galois_degree_coprime
    (V : Type uV) (L : Type uL)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] [IsGalois (FractionRing V) L]
    (p : ℕ) (hp : p.Prime) [CharP (V ⧸ IsLocalRing.maximalIdeal V) p]
    (hdegree : Nat.Coprime (Module.finrank (FractionRing V) L) p)
    (π : V) (hπ : Prime π) (n : ℕ) (hn : 0 < n)
    (hdiv : Module.finrank (FractionRing V) L ∣ n) :
    let W := AdjoinRoot (X ^ n - C π)
    let : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : IsDiscreteValuationRing W :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : Module.FaithfullyFlat V W := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
    let Kroot := FractionRing W
    let : Algebra (FractionRing V) Kroot := FractionRing.liftAlgebra V Kroot
    ∀ (m : Ideal (Kroot ⊗[FractionRing V] L)) [m.IsMaximal],
      let M := GenericTensorFieldComponent m
      let : Algebra W M := genericTensorFieldComponentLeftScalarAlgebra (R := W) m
      Algebra.Etale W (integralClosure W M) := by
  intro W hDomainW hDvrW hFlatW Kroot aKKroot m hm M aWM
  let K := FractionRing V
  have : IsScalarTower W Kroot M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let : Algebra V Vhat := standardDVFCompletionValuationSubringAlgebra V K
  have : IsLocalHom (algebraMap V Vhat) := standardDVRToCompletion_isLocalHom V K
  have hCharV : CharP (IsLocalRing.ResidueField V) p :=
    inferInstanceAs (CharP (V ⧸ IsLocalRing.maximalIdeal V) p)
  have : CharP H.residueField p :=
    ((IsLocalRing.ResidueField.map (algebraMap V Vhat)).charP_iff
      (RingHom.injective _) p).mp hCharV
  let aKKhat : Algebra K Khat := standardDVFCompletionAlgebra V K
  let : SMul K Khat := aKKhat.toSMul
  let πhat := standardDVRCompletionValuationSubringElement V K π
  have hπhat : H.valuation.IsUniformizer (πhat : Khat) :=
    standardDVRCompletionValuationSubringElement_isUniformizer
      V K π hπ.irreducible.maximalIdeal_eq
  let Rhat := AdjoinRoot (X ^ n - C πhat)
  have : IsDomain Rhat := completeDVFRootRing_isDomain H πhat hπhat n hn
  let Fhat := FractionRing Rhat
  let : Algebra Khat Fhat := completeDVFRootFractionFieldAlgebra H πhat hπhat n hn
  let : Algebra K Fhat := ((algebraMap Khat Fhat).comp (algebraMap K Khat)).toAlgebra
  have : IsScalarTower K Khat Fhat := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra W Rhat := standardDVRRootCompletionAlgebra V K n π
  have : Module.FaithfullyFlat W Rhat := standardDVRRootCompletion_faithfullyFlat V K n π
  have : FaithfulSMul W Fhat := FaithfulSMul.trans W Rhat Fhat
  let : Algebra Kroot Fhat := FractionRing.liftAlgebra W Fhat
  have : IsScalarTower W Kroot Fhat := FractionRing.isScalarTower_liftAlgebra W Fhat
  have : IsScalarTower K Kroot Fhat :=
    uniformizerRootCompletionFractionField_isScalarTower V n hn π hπ
  apply integralClosure_etale_of_standardCompletion_equiv_components W Kroot M Rhat Fhat
    (uniformizerRootStandardCompletionAlgEquiv V K n hn π hπ)
  intro qF hqF
  let PF := GenericTensorFieldComponent qF
  let : Algebra Rhat PF := genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) qF
  let q := genericTensorRefineChosenComponentIdeal
    (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  have : q.IsMaximal := genericTensorRefineChosenComponentIdeal_isMaximal
    (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  let Pq := GenericTensorFieldComponent q
  let : Algebra Rhat Pq := genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) q
  have : Algebra.Etale Rhat (integralClosure Rhat Pq) :=
    integralClosure_completeDVFRootTensorComponent_etale_of_galois_degree_coprime
      (K₀ := K) (L := L) H p hp hdegree πhat hπhat n hn hdiv q
  let e : integralClosure Rhat Pq ≃ₐ[Rhat] integralClosure Rhat PF :=
    genericTensorRefineChosenComponentIntegralClosureAlgEquiv
      (B := Rhat) (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  exact Algebra.Etale.of_equiv e

/-- The Galois degree itself gives an actual finite separable root extension
over which the normalization of the whole generic tensor product is finite
étale, with that tensor product as its generic fibre. -/
theorem finiteEtale_uniformizerGaloisDegreeRoot_normalization
    (V : Type uV) (L : Type uL)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] [IsGalois (FractionRing V) L]
    (p : ℕ) (hp : p.Prime) [CharP (V ⧸ IsLocalRing.maximalIdeal V) p]
    (hdegree : Nat.Coprime (Module.finrank (FractionRing V) L) p)
    (π : V) (hπ : Prime π) :
    let n := Module.finrank (FractionRing V) L
    let hn : 0 < n := Module.finrank_pos
    let W := AdjoinRoot (X ^ n - C π)
    let : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : IsDiscreteValuationRing W :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : Module.FaithfullyFlat V W := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
    let Kroot := FractionRing W
    let : Algebra (FractionRing V) Kroot := FractionRing.liftAlgebra V Kroot
    let G := Kroot ⊗[FractionRing V] L
    let : Algebra W G := genericTensorProductLeftScalarAlgebra
    Module.Finite (FractionRing V) Kroot ∧
      Algebra.IsSeparable (FractionRing V) Kroot ∧
        Module.finrank (FractionRing V) Kroot = n ∧
          Module.Finite W (integralClosure W G) ∧
            Algebra.Etale W (integralClosure W G) ∧
              Nonempty (Kroot ⊗[W] integralClosure W G ≃ₐ[Kroot] G) := by
  intro n hn W hDomainW hDvrW hFlatW Kroot aKKroot G aWG
  let K := FractionRing V
  have hnResidueUnit : IsUnit (n : V ⧸ IsLocalRing.maximalIdeal V) :=
    (CharP.isUnit_natCast_iff hp).mpr (hp.coprime_iff_not_dvd.mp hdegree.symm)
  have hnUnit : IsUnit (n : V) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_natCast]
    exact hnResidueUnit.ne_zero
  obtain ⟨hBaseFinite, hBaseSeparable, hBaseDegree⟩ :=
    uniformizerRoot_fractionField_finiteSeparable_degree hn hnUnit π hπ
  have hEtale : Algebra.Etale W (integralClosure W G) := by
    apply integralClosure_genericTensorProduct_etale
    intro m hm
    exact integralClosure_uniformizerRootTensorComponent_etale_of_galois_degree_coprime
      V L p hp hdegree π hπ n hn (dvd_refl n) m
  have : Algebra.FinitePresentation W (integralClosure W G) := hEtale.finitePresentation
  have hFiniteType : Algebra.FiniteType W (integralClosure W G) :=
    Algebra.FiniteType.of_finitePresentation (R := W) (A := integralClosure W G)
  have hFinite : Module.Finite W (integralClosure W G) :=
    Algebra.IsIntegral.finite (R := W) (A := integralClosure W G) (h' := hFiniteType)
  have : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  have : Module.Finite Kroot G := Module.Finite.base_change K Kroot L
  have : Algebra.Etale Kroot G := inferInstance
  have : IsScalarTower W Kroot G :=
    TensorProduct.isScalarTower_left (R := K) (R'₂ := W) (R' := Kroot)
  exact ⟨hBaseFinite, hBaseSeparable, hBaseDegree, hFinite, hEtale,
    ⟨SchemeTheory.integralClosureFiniteEtaleGenericFiberEquiv W Kroot G⟩⟩

end EtaleFundamentalGroups.Kummer
