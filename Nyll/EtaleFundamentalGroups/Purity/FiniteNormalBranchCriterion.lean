/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.RegularBoundaryPurity
public import Nyll.EtaleFundamentalGroups.Purity.Local.DimensionOne
public import Nyll.SchemeTheory.RingTheory.Dimension.PrimeContainingAtHeightOne
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension
public import Nyll.SchemeTheory.RingTheory.RegularLocal.Localization
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDimensionOne
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalTrace
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain

/-!
# Finite normal branch purity over a regular local ring

For an injective finite extension of a positive-dimensional regular local
ring by a normal domain, unramifiedness at the source height-one primes
implies etaleness. Going down retains the actual heights. At height one,
torsion-freeness over the base DVR supplies flatness. One such point also
supplies generic etaleness; the existing regular-boundary purity theorem
then removes the higher-codimension branch locus.

This is the finite dominant algebra step of Stacks Project, Tag 0BMB.
https://stacks.math.columbia.edu/tag/0BMB
-/

@[expose] public section

noncomputable section

open IsLocalRing
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula

namespace EtaleFundamentalGroups

universe u

/-- A finite injective normal-domain extension of a positive-dimensional
regular local ring is etale if the original height-one source primes are
unramified. Generic etaleness and flatness are constructed in the proof. -/
theorem finiteNormalDomainAlgebra_etale_of_isUnramifiedAt_height_one
    {R S : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (hunramified : ∀ (Q : Ideal S) [Q.IsPrime], Q.height = 1 →
      Algebra.IsUnramifiedAt R Q) : Algebra.Etale R S := by
  let : IsDomain R := IsRegularLocalRing.isDomain R
  let : IsIntegrallyClosed R := SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing R
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  let : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finitePresentation R S
  have hlocal (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
      Algebra.Etale (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) := by
    let Rₚ := Localization.AtPrime p
    let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    let : IsRegularLocalRing Rₚ :=
      SchemeTheory.RegularLocalResolution.isRegularLocalRing_localizationAtPrime R p
    have hdimₚ : ringKrullDim Rₚ = (1 : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rₚ, hp]
      rfl
    let : IsDiscreteValuationRing Rₚ :=
      SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one Rₚ hdimₚ
    let : Module.IsTorsionFree Rₚ Sₚ :=
      Module.IsTorsionFree.of_isLocalization R S p.primeCompl_le_nonZeroDivisors
    let : Module.Finite Rₚ Sₚ := inferInstance
    let : Algebra.IsIntegral Rₚ Sₚ := Algebra.IsIntegral.of_finite Rₚ Sₚ
    apply etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
    intro q _
    let Q : Ideal S := q.under S
    have hpq : Q.under R = p := by
      have hm : q.under Rₚ = maximalIdeal Rₚ :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q)
      calc
        Q.under R = (q.under Rₚ).under R := by rw [Ideal.under_under, Ideal.under_under]
        _ = (maximalIdeal Rₚ).under R := congrArg (fun I : Ideal Rₚ ↦ I.under R) hm
        _ = p := IsLocalization.AtPrime.under_maximalIdeal Rₚ p
    have hQheight : Q.height = 1 := by
      rw [height_eq_height_under_of_hasGoingDown (R := R) Q, hpq]
      exact hp
    let : Algebra.IsUnramifiedAt R Q := hunramified Q hQheight
    let e : Localization.AtPrime Q ≃ₐ[S] Localization.AtPrime q :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Algebra.algebraMapSubmonoid S p.primeCompl) q
    let : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
      Algebra.FormallyUnramified.of_equiv (e.restrictScalars R)
    exact Algebra.FormallyUnramified.of_restrictScalars R Rₚ (Localization.AtPrime q)
  have hheightOne (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
      (P : Ideal S) [P.IsPrime] [P.LiesOver p] : Algebra.IsEtaleAt R P := by
    apply SpecialLocalPurity.isEtaleAt_of_localizedAlgebra_etale ⟨p, inferInstance⟩
      (hlocal p hp) ⟨P, inferInstance⟩
    apply PrimeSpectrum.ext
    exact (Ideal.over_def P p).symm
  have hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S) := by
    obtain ⟨p, hp, _, hheight⟩ := SchemeTheory.exists_height_one_prime_containing
      R hdim (0 : R) (Ideal.zero_mem (maximalIdeal R))
    let : p.IsPrime := hp
    obtain ⟨P, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := S) p (by
        intro r hr
        have hr0 : r = 0 := hinj (hr.trans (map_zero (algebraMap R S)).symm)
        exact hr0.symm ▸ p.zero_mem)
    let : P.IsPrime := hP
    let : P.LiesOver p := ⟨hPp.symm⟩
    exact Algebra.isOpen_etaleLocus.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes ⟨⊥, inferInstance⟩ ⟨P, inferInstance⟩).mp bot_le)
      (hheightOne p hheight P)
  apply SpecialLocalPurity.finiteNormalDomainAlgebra_etale_of_regular_boundary
    hinj Set.univ (fun p _ ↦
      SchemeTheory.RegularLocalResolution.isRegularLocalRing_localizationAtPrime R p.asIdeal)
    hgeneric (fun _ h ↦ False.elim (h (Set.mem_univ _))) hheightOne

end EtaleFundamentalGroups
