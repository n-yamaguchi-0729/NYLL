/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Chosen.DVRProductCoordinate
import Nyll.EtaleFundamentalGroups.Completions.Chosen.GenericComponent
import Nyll.EtaleFundamentalGroups.Completions.DVR.IntegralExtensionEtaleDescent
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.Completion
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.CompletionAdic
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.CompletionResidue
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerCompletion
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerCompletionTower
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.ComponentPrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.Completions.RootTensor.EtalePrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.Refinement.NormalizationLocal
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.RootCompletionBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.NormalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Removing ramification by a uniformizer root over an arbitrary DVR

Let `V` be a DVR with residue characteristic zero, and let `C` be a finite
integral Dedekind extension with fraction field `L`. If all branch indices
divide `n`, form the actual root DVR `W = V[X] / (X ^ n - π)`.

For every field component of `Frac(W) ⊗[Frac(V)] L`, its integral closure
over `W` is étale. We use the actual standard completion of `W`, identify
it with the completed root ring, and refine the original tensor component
in that completed field. The completed Abhyankar theorem then applies to
that same component. The product of all completed normalization factors
and faithful flatness descend étaleness to `W`.

Completeness, an ambient regular surface, and an assumed normalization
comparison are absent from the hypotheses. This is the local normalized
base-change step in Stacks Project, Proposition 58.30.2:
https://stacks.math.columbia.edu/tag/0C0Q.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uV uC uL uRhat uFhat

/-- Complete the actual normalization, identify its completed base with
`Rhat`, and descend the étaleness of every transported tensor component.
The public uniformizer theorem constructs both inputs to this helper. -/
theorem integralClosure_etale_of_standardCompletion_equiv_components
    (W : Type uV) (K : Type uC) (M : Type uL)
    (Rhat : Type uRhat) (Fhat : Type uFhat)
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field K] [Algebra W K] [IsFractionRing W K]
    [Field M] [Algebra K M] [Algebra W M] [IsScalarTower W K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [CommRing Rhat] [Algebra W Rhat]
    [Field Fhat] [Algebra Rhat Fhat] [IsFractionRing Rhat Fhat]
    [Algebra W Fhat] [IsScalarTower W Rhat Fhat]
    [Algebra K Fhat] [IsScalarTower W K Fhat]
    (eBase :
      let Hw := standardDVFCompletionCompleteDVF W K
      let What := Hw.valuationSubring
      let : Algebra W What := standardDVFCompletionValuationSubringAlgebra W K
      What ≃ₐ[W] Rhat)
    (hlocal : ∀ (qF : Ideal (Fhat ⊗[K] M)) [qF.IsMaximal],
      let : Algebra Rhat (GenericTensorFieldComponent qF) :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) qF
      Algebra.Etale Rhat (integralClosure Rhat (GenericTensorFieldComponent qF))) :
    Algebra.Etale W (integralClosure W M) := by
  classical
  let Croot := integralClosure W M
  have : IsFractionRing Croot M :=
    IsIntegralClosure.isFractionRing_of_finite_extension W K M Croot
  have : IsDedekindDomain Croot := IsIntegralClosure.isDedekindDomain W K M Croot
  have : Module.IsTorsionFree W M := Module.IsTorsionFree.trans_faithfulSMul W K M
  have : Module.IsTorsionFree W Croot := IsIntegralClosure.isTorsionFree W M
  have : Module.Finite W Croot := IsIntegralClosure.finite W K M Croot
  apply etale_of_completedPrimeValuationSubring_etale
    (V := W) (C := Croot) (K := K) (L := M)
  intro pRoot Hw What Aroot Qroot
  let : Algebra W What := standardDVFCompletionValuationSubringAlgebra W K
  let : ∀ Q, Algebra What (Aroot Q) := fun Q ↦
    completedPrimeValuationSubringCompletionAlgebra
      (V := W) (C := Croot) (K := K) (L := M) Q
  let Lhat := standardDVFCompletionField W K
  have : IsLocalHom (algebraMap W What) := standardDVRToCompletion_isLocalHom W K
  have : Module.FaithfullyFlat W What :=
    standardDVRCompletionValuationSubring_faithfullyFlat (V := W) (K := K)
  let aKLhat : Algebra K Lhat := standardDVFCompletionAlgebra W K
  let aWLhat : Algebra W Lhat := standardDVFCompletionBaseAlgebra (V := W) (K := K)
  let : SMul K Lhat := aKLhat.toSMul
  let : Module K Lhat := aKLhat.toModule
  let : SMul W Lhat := aWLhat.toSMul
  have : IsScalarTower W K Lhat :=
    standardDVFCompletion_isScalarTower (V := W) (K := K)
  let : Algebra What Lhat := Algebra.ofSubsemiring Hw.valuation.valuationSubring
  have : IsScalarTower W What Lhat :=
    standardDVRCompletionValuationSubring_isScalarTower (V := W) (K := K)
  have hmax : (IsLocalRing.maximalIdeal W).map (algebraMap W What) =
      IsLocalRing.maximalIdeal What := standardDVRToCompletion_maximalIdeal_map_eq W K
  have hres : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap W What)) :=
    standardDVRToCompletion_residueFieldMap_bijective W K
  let qstd : Ideal (Lhat ⊗[K] M) := completedGenericTensorChosenIdeal
    (R := W) (R' := What) (C := Croot) (K := K) (L := M)
    (K' := Lhat) hmax hres Qroot.1
  have : qstd.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
    (R := W) (R' := What) (C := Croot) (K := K) (L := M)
    (K' := Lhat) hmax hres Qroot.1
  have : IsFractionRing What Lhat := Hw.toDVF.valuationSubring_isFractionRing
  let eField : Lhat ≃ₐ[K] Fhat :=
    IsFractionRing.fieldEquivOfAlgEquiv K Lhat Fhat eBase
  have : IsScalarTower K K Lhat := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K K Fhat := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eTensor : (Lhat ⊗[K] M) ≃ₐ[K] (Fhat ⊗[K] M) :=
    Algebra.TensorProduct.congr eField (AlgEquiv.refl : M ≃ₐ[K] M)
  let qF : Ideal (Fhat ⊗[K] M) := qstd.map eTensor.toRingEquiv
  have : qF.IsMaximal := (inferInstance : qstd.IsMaximal).map_bijective
    (f := eTensor.toRingEquiv) eTensor.bijective
  let eQuot : GenericTensorFieldComponent qstd ≃ₐ[K]
      GenericTensorFieldComponent qF := Ideal.quotientEquivAlg qstd qF eTensor rfl
  let Pstd := GenericTensorFieldComponent qstd
  let PF := GenericTensorFieldComponent qF
  let : Algebra Rhat PF := genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) qF
  have hPF : Algebra.Etale Rhat (integralClosure Rhat PF) := hlocal qF
  have heQuot (z : Lhat) : eQuot (algebraMap Lhat Pstd z) =
      algebraMap Fhat PF (eField z) := by
    change Ideal.Quotient.mk qF (eTensor (z ⊗ₜ[K] (1 : M))) =
      Ideal.Quotient.mk qF (eField z ⊗ₜ[K] (1 : M))
    apply congrArg (Ideal.Quotient.mk qF)
    exact Algebra.TensorProduct.map_tmul
      (eField : Lhat →ₐ[K] Fhat) (AlgHom.id K M) z 1
  have hcompat : eQuot.toRingEquiv.toRingHom.comp (algebraMap What Pstd) =
      (algebraMap Rhat PF).comp eBase.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro x
    change eQuot (algebraMap What Pstd x) = algebraMap Rhat PF (eBase x)
    calc
      eQuot (algebraMap What Pstd x) =
          algebraMap Fhat PF (eField (algebraMap What Lhat x)) :=
        heQuot (algebraMap What Lhat x)
      _ = algebraMap Fhat PF (algebraMap Rhat Fhat (eBase x)) :=
        congrArg (algebraMap Fhat PF)
          (IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K Lhat Fhat eBase x)
      _ = algebraMap Rhat PF (eBase x) := rfl
  have hStd : Algebra.Etale What (integralClosure What Pstd) :=
    integralClosure_etale_of_baseAndAmbientEquiv
      eBase.toRingEquiv eQuot.toRingEquiv hcompat hPF
  let eChosen : integralClosure What Pstd ≃ₐ[What] Aroot Qroot :=
    completedGenericTensorChosenIntegralClosureAlgEquiv
      (V := W) (C := Croot) (K := K) (L := M) Qroot
  exact Algebra.Etale.of_equiv eChosen

/-- A common multiple of the actual branch indices removes ramification
after adjoining that root of a uniformizer. The conclusion concerns the
literal maximal-ideal quotient of the original generic tensor product. -/
theorem integralClosure_uniformizerRootTensorComponent_etale_of_ramification_dvd
    {V : Type uV} {C : Type uC}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [Algebra.IsIntegral V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra (FractionRing V) L] [IsScalarTower V (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] [Algebra.IsSeparable (FractionRing V) L]
    (π : V) (hπ : Prime π) (n : ℕ) (hn : 0 < n)
    (hdiv : ∀ Q : (IsLocalRing.maximalIdeal V).primesOver C,
      Q.1.ramificationIdx V ∣ n)
    (hCharZero : CharZero (V ⧸ IsLocalRing.maximalIdeal V)) :
    let W := AdjoinRoot (X ^ n - Polynomial.C π)
    let : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : IsDiscreteValuationRing W :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : Module.FaithfullyFlat V W := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
    let Kroot := FractionRing W
    let : Algebra (FractionRing V) Kroot := FractionRing.liftAlgebra V Kroot
    ∀ (m : Ideal (Kroot ⊗[FractionRing V] L)) (hm : m.IsMaximal),
      let : m.IsMaximal := hm
      let M := GenericTensorFieldComponent m
      let : Algebra W M := genericTensorFieldComponentLeftScalarAlgebra (R := W) m
      Algebra.Etale W (integralClosure W M) := by
  intro W hDomainW hDvrW hFlatW Kroot aKKroot m hm hmInstance M aWM
  classical
  let K := FractionRing V
  have : IsScalarTower V K Kroot := FractionRing.isScalarTower_liftAlgebra V Kroot
  have : IsScalarTower W Kroot M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let : Algebra V Vhat := standardDVFCompletionValuationSubringAlgebra V K
  have : IsLocalHom (algebraMap V Vhat) := standardDVRToCompletion_isLocalHom V K
  have : Module.FaithfullyFlat V Vhat :=
    standardDVRCompletionValuationSubring_faithfullyFlat (V := V) (K := K)
  let aKKhat : Algebra K Khat := standardDVFCompletionAlgebra V K
  let aVKhat : Algebra V Khat := standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat := aKKhat.toSMul
  let : SMul V Khat := aVKhat.toSMul
  have : IsScalarTower V K Khat := standardDVFCompletion_isScalarTower (V := V) (K := K)
  have : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower (V := V) (K := K)
  have hπmax : IsLocalRing.maximalIdeal V = Ideal.span ({π} : Set V) :=
    hπ.irreducible.maximalIdeal_eq
  let πhat := standardDVRCompletionValuationSubringElement V K π
  have hπhat : H.valuation.IsUniformizer (πhat : Khat) :=
    standardDVRCompletionValuationSubringElement_isUniformizer V K π hπmax
  let Rhat := AdjoinRoot (X ^ n - Polynomial.C πhat)
  have : IsDomain Rhat := completeDVFRootRing_isDomain H πhat hπhat n hn
  let Fhat := FractionRing Rhat
  let : Algebra Khat Fhat := completeDVFRootFractionFieldAlgebra H πhat hπhat n hn
  have : IsScalarTower Vhat Khat Fhat :=
    completeDVFRootFractionField_isScalarTower H πhat hπhat n hn
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
  let q : Ideal (Fhat ⊗[K] L) := genericTensorRefineChosenComponentIdeal
    (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  have : q.IsMaximal := genericTensorRefineChosenComponentIdeal_isMaximal
    (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  let Pq := GenericTensorFieldComponent q
  let : Algebra Rhat Pq := genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) q
  have hRoot : Algebra.Etale Rhat (integralClosure Rhat Pq) :=
    integralClosure_completedRootTensorComponent_etale_of_ramification_dvd
      (V := V) (C := C) (K := K) (L := L) π hπmax n hn hdiv hCharZero q inferInstance
  let eNormalization : integralClosure Rhat Pq ≃ₐ[Rhat] integralClosure Rhat PF :=
    genericTensorRefineChosenComponentIntegralClosureAlgEquiv
      (B := Rhat) (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  exact Algebra.Etale.of_equiv eNormalization

end EtaleFundamentalGroups.Kummer
