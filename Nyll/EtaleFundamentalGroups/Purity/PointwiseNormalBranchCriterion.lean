/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The local smooth-fiber comparison adapts the localization setup in
`Algebra.IsSmoothAt.of_formallySmooth_fiber`, Mathlib/RingTheory/Smooth/Fiber.lean:
Copyright (c) 2026 Andrew Yang; Authors: Andrew Yang; Apache 2.0.
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.FiniteNormalBranchCriterion
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleFiniteFactor
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalNormality
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleSource
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension
public import Nyll.SchemeTheory.RingTheory.Ramification.Trace.PointwiseFlatPurity
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalLocalizationAtPrimeEtale
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.TensorProduct.Maps
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain

/-!
# Pointwise normal branch purity

At a quasi-finite prime with normal source local ring and regular target
local ring of the same positive dimension, source codimension-one
unramifiedness implies etaleness. The constructed finite local factor is
normal. Equality of the original local dimensions forces the finite base
map to be injective; it is not imposed as an extra dominance hypothesis.
The finite normal branch criterion and faithfully flat descent then apply.

This is the affine algebra form of Stacks Project, Tag 0BMB.
https://stacks.math.columbia.edu/tag/0BMB
-/

@[expose] public section

noncomputable section

open IsLocalRing
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

private theorem injective_of_isIntegral_of_eq_ringKrullDim
    {A C : Type u} [CommRing A] [CommRing C]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra A C] [Algebra.IsIntegral A C]
    (hdim : ringKrullDim A = ringKrullDim C) :
    Function.Injective (algebraMap A C) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨r, hrker, hrne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let K := RingHom.ker (algebraMap A C)
  let Ak := A ⧸ K
  let φ : Ak →+* C := RingHom.kerLift (algebraMap A C)
  let : Algebra Ak C := φ.toAlgebra
  let : IsScalarTower A Ak C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (RingHom.kerLift_mk (algebraMap A C) a).symm)
  let : Algebra.IsIntegral Ak C := Algebra.IsIntegral.tower_top A
  have hkd : ringKrullDim Ak = ringKrullDim C :=
    ringKrullDim_eq_of_isIntegral_of_injective (RingHom.kerLift_injective (algebraMap A C))
  have hle : ringKrullDim Ak + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hrne) (Ideal.Quotient.eq_zero_iff_mem.mpr hrker)
  rw [hkd, ← hdim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)] at hle
  have hle' : (maximalIdeal A).height + 1 ≤ (maximalIdeal A).height := by
    exact_mod_cast hle
  have hfinite : (maximalIdeal A).height ≠ ⊤ :=
    ((maximalIdeal A).height_le_spanFinrank Ideal.IsPrime.ne_top').trans_lt
      (ENat.natCast_lt_top _) |>.ne
  exact (lt_irrefl (maximalIdeal A).height) ((ENat.add_one_le_iff hfinite).mp hle')

private theorem isEtaleAt_of_isUnramifiedAt_of_flat_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)] [Algebra.IsUnramifiedAt R q] :
    Algebra.IsEtaleAt R q := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : IsLocalHom (algebraMap Rp Sq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  let : Module.Flat Rp Sq :=
    (Module.flat_iff_of_isLocalization Rp p.primeCompl Sq).mpr inferInstance
  let : Algebra.FormallyUnramified Rp Sq :=
    Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  have hle : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := by
    rintro s ⟨r, hr, rfl⟩
    exact hr
  let : Algebra Sp Sq := IsLocalization.localizationAlgebraOfSubmonoidLe
    Sp Sq (Algebra.algebraMapSubmonoid S p.primeCompl) q.primeCompl hle
  let : IsScalarTower S Sp Sq := IsLocalization.localization_isScalarTower_of_submonoid_le
    Sp Sq (Algebra.algebraMapSubmonoid S p.primeCompl) q.primeCompl hle
  let : IsScalarTower R Sp Sq := IsScalarTower.to₁₃₄ R S Sp Sq
  let : IsScalarTower Rp Sp Sq := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  let : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    IsLocalization.isLocalization_of_submonoid_le Sp Sq
      (Algebra.algebraMapSubmonoid S p.primeCompl) q.primeCompl hle
  let : Algebra.IsPushout R Rp S Sp :=
    (Algebra.isPushout_of_isLocalization p.primeCompl Rp S Sp).symm
  let : Algebra.FinitePresentation Rp Sp :=
    Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv R Rp S Sp)
  let : Algebra.FormallyEtale (ResidueField Rp) (ResidueField Rp ⊗[Rp] Sq) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  let : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (R := Rp) (S := Sq) (P := Sp) (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  let : Algebra.FormallySmooth R Sq := Algebra.FormallySmooth.comp R Rp Sq
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- Stacks Project, Tag 0BMB, in affine algebra form. The equality of
source and target local dimensions is retained and used to prove the
injectivity needed by finite normal branch purity. -/
theorem isEtaleAt_of_normal_of_regular_of_quasiFiniteAt_of_isUnramifiedAt_height_one
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q]
    [IsDomain (Localization.AtPrime q)] [IsIntegrallyClosed (Localization.AtPrime q)]
    [IsRegularLocalRing (Localization.AtPrime (q.under R))]
    (hdim : q.height = (q.under R).height) (hqheight : 1 ≤ q.height)
    (hunramified : ∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 →
      Algebra.IsUnramifiedAt R q') : Algebra.IsEtaleAt R q := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let p := q.under R
  obtain ⟨R', _, _, _, P, _, _, e, _, hfinite, Q, hQ, hQP, hQq, hQunique⟩ :=
    SchemeTheory.exists_etale_finite_factor_prime_of_quasiFiniteAt p q
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
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : Module.Flat Sq C :=
    (Module.flat_iff_of_isLocalization Sq q.primeCompl C).mpr inferInstance
  let : IsLocalHom (algebraMap Sq C) := by
    rw [Localization.AtPrime.algebraMap_eq q Q]
    infer_instance
  let : Module.FaithfullyFlat Sq C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra.FormallyEtale Sq C := Algebra.FormallyEtale.of_restrictScalars (R := S)
  have hQspec : (⟨Q.under S, inferInstance⟩ : PrimeSpectrum S) = ⟨q, inferInstance⟩ :=
    PrimeSpectrum.ext hQq
  let : IsDomain (Localization.AtPrime (Q.under S)) :=
    (congrArg (fun r : PrimeSpectrum S => IsDomain (Localization.AtPrime r.asIdeal))
      hQspec).mpr inferInstance
  let : IsIntegrallyClosed (Localization.AtPrime (Q.under S)) :=
    (congrArg (fun r : PrimeSpectrum S => IsIntegrallyClosed (Localization.AtPrime r.asIdeal))
      hQspec).mpr inferInstance
  have hnormal := SchemeTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale S D Q
  let : IsDomain C := hnormal.1
  let : IsIntegrallyClosed C := hnormal.2
  have hPp : P.under R = p := (P.over_def p).symm
  have hPspec : (⟨P.under R, inferInstance⟩ : PrimeSpectrum R) = ⟨p, inferInstance⟩ :=
    PrimeSpectrum.ext hPp
  have hregular : IsRegularLocalRing (Localization.AtPrime (P.under R)) :=
    (congrArg (fun r : PrimeSpectrum R => IsRegularLocalRing (Localization.AtPrime r.asIdeal))
      hPspec).mpr inferInstance
  let : IsRegularLocalRing A :=
    isRegularLocalRing_localization_atPrime_of_etale_of_comap R R' P hregular
  let : IsDomain A := IsRegularLocalRing.isDomain A
  have hCdim : ringKrullDim C = (q.height : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q C,
      SchemeTheory.height_eq_height_under_of_flat_of_formallyUnramified (R := S) Q, hQq]
  have hAdim : ringKrullDim A = (p.height : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P A,
      SchemeTheory.height_eq_height_under_of_flat_of_formallyUnramified (R := R) P, hPp]
  have hACdim : ringKrullDim A = ringKrullDim C := by rw [hAdim, hCdim, hdim]
  have hApositive : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [hACdim, hCdim]
    exact_mod_cast hqheight
  have hinj : Function.Injective (algebraMap A C) :=
    injective_of_isIntegral_of_eq_ringKrullDim hACdim
  let : Algebra.Etale A C := finiteNormalDomainAlgebra_etale_of_isUnramifiedAt_height_one
    hinj hApositive (by
      intro J _ hJheight
      let Jd := J.under D
      let Js := Jd.under S
      have hJdQ : Jd ≤ Q :=
        ((IsLocalization.AtPrime.orderIsoOfPrime C Q) ⟨J, inferInstance⟩).2.2
      have hJsq : Js ≤ q := hQq ▸ Ideal.comap_mono hJdQ
      have hJsheight : Js.height = 1 := by
        rw [← SchemeTheory.height_eq_height_under_of_flat_of_formallyUnramified (R := S) Jd,
          IsLocalization.height_under Q.primeCompl J]
        exact hJheight
      let : Algebra.IsUnramifiedAt R Js := hunramified Js hJsq hJsheight
      let : Algebra.IsUnramifiedAt R Jd := Algebra.IsUnramifiedAt.comp Js Jd
      let : Algebra.IsUnramifiedAt R J := Algebra.IsUnramifiedAt.comp Jd J
      exact Algebra.FormallyUnramified.of_restrictScalars R A (Localization.AtPrime J))
  let : Algebra.FormallyEtale R A := Algebra.FormallyEtale.comp R R' A
  let : Algebra.FormallyEtale R C := Algebra.FormallyEtale.comp R A C
  let : Module.Flat R C := Module.Flat.trans R A C
  let : Module.Flat R Sq := SchemeTheory.flat_of_faithfullyFlat_of_flat R Sq C
  have : Subsingleton (C ⊗[Sq] Ω[Sq⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Sq C).subsingleton
  have : Subsingleton Ω[Sq⁄R] :=
    Module.FaithfullyFlat.lTensor_reflects_triviality Sq C Ω[Sq⁄R]
  let : Algebra.IsUnramifiedAt R q := ⟨inferInstance⟩
  exact isEtaleAt_of_isUnramifiedAt_of_flat_localization q

end EtaleFundamentalGroups
