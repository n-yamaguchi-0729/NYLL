/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Ramification.Trace.FiniteFlatHeightOneCriterion
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleFiniteFactor
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The pointwise flat purity criterion

The actual quasi-finite local structure theorem constructs a finite factor
with a unique point over a selected etale base point. Localizing that factor
is finite over the localized base, so the finite flat discriminant criterion
applies. Heights and the original unramified maps are transported through
the actual etale source map. Faithfully flat descent of differentials then
recovers unramifiedness at the original source prime.

This is the affine algebra form of Stacks Project, Tag 0BJH.
https://stacks.math.columbia.edu/tag/0BJH
-/

@[expose] public section

noncomputable section

open IsLocalRing
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula
open scoped TensorProduct

namespace SchemeTheory

universe u v

/-- Flat unramified extensions preserve the height of each original prime. -/
theorem height_eq_height_under_of_flat_of_formallyUnramified
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FormallyUnramified R S]
    [Algebra.EssFiniteType R S] (Q : Ideal S) [Q.IsPrime] :
    Q.height = (Q.under R).height := by
  let p := Q.under R
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization.AtPrime Q
  let : Algebra Rₚ Sₚ := Localization.AtPrime.algebraOfLiesOver p Q
  let : IsLocalHom (algebraMap Rₚ Sₚ) := by
    rw [Localization.AtPrime.algebraMap_eq p Q]
    infer_instance
  let : Module.Flat Rₚ Sₚ :=
    (Module.flat_iff_of_isLocalization Rₚ p.primeCompl Sₚ).mpr inferInstance
  let : Algebra.FormallyUnramified Rₚ Sₚ :=
    Algebra.FormallyUnramified.of_restrictScalars R Rₚ Sₚ
  let : Algebra.EssFiniteType Rₚ Sₚ := Algebra.EssFiniteType.of_comp R Rₚ Sₚ
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal Rₚ) (maximalIdeal Sₚ)
  rw [Algebra.FormallyUnramified.map_maximalIdeal] at h
  have hheight : (maximalIdeal Sₚ).height = (maximalIdeal Rₚ).height := by
    simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h
  have hdim : ringKrullDim Sₚ = ringKrullDim Rₚ := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Sₚ),
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Rₚ), hheight]
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q Sₚ,
    IsLocalization.AtPrime.ringKrullDim_eq_height p Rₚ] at hdim
  exact WithBot.coe_injective hdim

/-- A flat finite-type algebra over a Noetherian ring is etale at a
positive-height quasi-finite prime if the original algebra is unramified at
every height-one prime specializing to it. No finite factor, local
comparison, or etale neighborhood is supplied as an assumption. -/
theorem isEtaleAt_of_flat_of_quasiFiniteAt_of_isUnramifiedAt_height_one
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q]
    (hqheight : 1 ≤ q.height)
    (hunramified : ∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 →
      Algebra.IsUnramifiedAt R q') : Algebra.IsEtaleAt R q := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let p := q.under R
  obtain ⟨R', _, _, _, P, _, _, e, _, hfinite, Q, hQ, hQP, hQq, hQunique⟩ :=
    exists_etale_finite_factor_prime_of_quasiFiniteAt p q
  let B := R' ⊗[R] S
  let : Algebra S B := Algebra.TensorProduct.rightAlgebra
  let : Algebra.Etale S B :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight R S R')
  let D := Localization.Away e
  let : Algebra.Etale S D := Algebra.Etale.comp S B D
  let : Module.Finite R' D := hfinite
  let : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  let : IsNoetherianRing D := IsNoetherianRing.of_finite R' D
  let : Q.IsPrime := hQ
  let : Q.LiesOver P := hQP
  let : Q.LiesOver q := ⟨hQq.symm⟩
  let A := Localization.AtPrime P
  let C := Localization.AtPrime Q
  let Sq := Localization.AtPrime q
  let : Algebra A C := Localization.AtPrime.algebraOfLiesOver P Q
  let : Algebra Sq C := Localization.AtPrime.algebraOfLiesOver q Q
  let : Module.Finite A C := Localization.finite_of_primesOver_eq_singleton hQunique
  let : Module.Flat A C :=
    (Module.flat_iff_of_isLocalization A P.primeCompl C).mpr inferInstance
  let : Module.Flat Sq C :=
    (Module.flat_iff_of_isLocalization Sq q.primeCompl C).mpr inferInstance
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap Sq C) := by
    rw [Localization.AtPrime.algebraMap_eq q Q]
    infer_instance
  let : Module.FaithfullyFlat Sq C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra.FormallyEtale Sq C :=
    Algebra.FormallyEtale.of_restrictScalars (R := S)
  have hCdim : ringKrullDim C = (q.height : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q C,
      height_eq_height_under_of_flat_of_formallyUnramified (R := S) Q, hQq]
  have hACdim : ringKrullDim C = ringKrullDim A := by
    have hmax : (maximalIdeal C).under A = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal C))
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := C),
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A),
      height_eq_height_under_of_hasGoingDown (R := A) (maximalIdeal C), hmax]
  have hAdim : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [← hACdim, hCdim]
    exact_mod_cast hqheight
  let : Algebra.Etale A C := etale_of_finite_flat_of_isUnramifiedAt_height_one hAdim (by
    intro J _ hJheight
    let Jd := J.under D
    let Js := Jd.under S
    have hJdQ : Jd ≤ Q :=
      ((IsLocalization.AtPrime.orderIsoOfPrime C Q) ⟨J, inferInstance⟩).2.2
    have hJsq : Js ≤ q := hQq ▸ Ideal.comap_mono hJdQ
    have hJsheight : Js.height = 1 := by
      rw [← height_eq_height_under_of_flat_of_formallyUnramified (R := S) Jd,
        IsLocalization.height_under Q.primeCompl J]
      exact hJheight
    let : Algebra.IsUnramifiedAt R Js := hunramified Js hJsq hJsheight
    let : Algebra.IsUnramifiedAt R Jd := Algebra.IsUnramifiedAt.comp Js Jd
    let : Algebra.IsUnramifiedAt R J := Algebra.IsUnramifiedAt.comp Jd J
    exact Algebra.FormallyUnramified.of_restrictScalars R A (Localization.AtPrime J))
  let : Algebra.FormallyEtale R A := Algebra.FormallyEtale.comp R R' A
  let : Algebra.FormallyEtale R C := Algebra.FormallyEtale.comp R A C
  have : Subsingleton (C ⊗[Sq] Ω[Sq⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Sq C).subsingleton
  have : Subsingleton Ω[Sq⁄R] :=
    Module.FaithfullyFlat.lTensor_reflects_triviality Sq C Ω[Sq⁄R]
  let : Algebra.IsUnramifiedAt R q := ⟨inferInstance⟩
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := R) (S := S) q

end SchemeTheory
