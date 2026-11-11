/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Dimension.PrimeContainingAtHeightOne
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension
public import Nyll.SchemeTheory.RingTheory.Ramification.Trace.FiniteFreeDiscriminant
public import Nyll.SchemeTheory.FiniteEtale.Local.OfTargetLocalizations
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Finite flat branch detection in codimension one

A finite flat algebra over a positive-dimensional Noetherian local ring
is etale when it is unramified at all height-one source primes. The trace
discriminant detects failure of etaleness. The actual height-one-prime
existence theorem applies even to zero divisors, so no domain assumption
on the base is introduced. Integral going down identifies source heights,
and iterated localization transports the original unramified local maps.

This is the finite-algebra local step of Stacks Project, Tag 0BJH.
https://stacks.math.columbia.edu/tag/0BJH
-/

@[expose] public section

noncomputable section

open IsLocalRing Module
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula

namespace SchemeTheory

universe u v

/-- In a positive-dimensional Noetherian local ring, being a unit is
detected at the height-one localizations, including for zero divisors. -/
theorem isUnit_of_height_one_localizations_of_positive_dimension
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R) (a : R)
    (hlocal : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap R (Localization.AtPrime p) a)) : IsUnit a := by
  by_contra hunit
  have ha : a ∈ maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hunit
  obtain ⟨p, hp, hap, hpheight⟩ := exists_height_one_prime_containing R hdim a ha
  let : p.IsPrime := hp
  have hmem : algebraMap R (Localization.AtPrime p) a ∈
      maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p a).mpr hap
  have hnonunit : ¬ IsUnit (algebraMap R (Localization.AtPrime p) a) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmem
  exact hnonunit (hlocal p hpheight)

/-- A finite free algebra over a positive-dimensional Noetherian local
ring is etale if all its height-one base localizations are etale. -/
theorem etale_of_finite_free_of_height_one_localizations
    {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (hlocal : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Algebra.Etale (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) :
    Algebra.Etale R S := by
  let ι := Module.Free.ChooseBasisIndex R S
  let : Fintype ι := Fintype.ofFinite ι
  let : DecidableEq ι := Classical.decEq ι
  let b : Basis ι R S := Module.Free.chooseBasis R S
  apply (EtaleFundamentalGroups.etale_iff_isUnit_discr b).mpr
  apply isUnit_of_height_one_localizations_of_positive_dimension hdim
  intro p _ hp
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : Algebra.Etale Rₚ Sₚ := hlocal p hp
  let bₚ : Basis ι Rₚ Sₚ := b.localizationLocalization Rₚ p.primeCompl Sₚ
  have hunit : IsUnit (Algebra.discr Rₚ bₚ) :=
    (EtaleFundamentalGroups.formallyUnramified_iff_isUnit_discr bₚ).mp inferInstance
  rw [Algebra.discr_localizationLocalization R p.primeCompl Sₚ b] at hunit
  exact hunit

/-- The finite flat local branch criterion: source codimension-one
unramifiedness implies etaleness, without normality or regularity of the
base. All local comparisons use the original algebra and its actual primes. -/
theorem etale_of_finite_flat_of_isUnramifiedAt_height_one
    {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Finite R S]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (hunramified : ∀ (Q : Ideal S) [Q.IsPrime], Q.height = 1 →
      Algebra.IsUnramifiedAt R Q) :
    Algebra.Etale R S := by
  let : Module.Free R S := Module.free_of_flat_of_isLocalRing
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  apply etale_of_finite_free_of_height_one_localizations hdim
  intro p _ hp
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Basis ι R S := Module.Free.chooseBasis R S
  let bₚ : Basis ι Rₚ Sₚ := b.localizationLocalization Rₚ p.primeCompl Sₚ
  let : Module.Free Rₚ Sₚ := Module.Free.of_basis bₚ
  let : Module.Finite Rₚ Sₚ := inferInstance
  let : Algebra.IsIntegral Rₚ Sₚ := Algebra.IsIntegral.of_finite Rₚ Sₚ
  let : Module.FinitePresentation Rₚ Sₚ := Module.finitePresentation_of_projective Rₚ Sₚ
  let : Algebra.FinitePresentation Rₚ Sₚ := inferInstance
  apply EtaleFundamentalGroups.etale_of_isEtaleAt_all_maximalIdeals
  intro q hq
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
  let : Algebra.IsUnramifiedAt Rₚ q :=
    Algebra.FormallyUnramified.of_restrictScalars R Rₚ (Localization.AtPrime q)
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := Rₚ) (S := Sₚ) q

end SchemeTheory
