/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.NormalDomainRoot
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootDivisorNormalization
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.SmoothBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.LocalizedComponent
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponentEtale
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.RegularBoundaryPurity
import Nyll.SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.PrimeFractionRing
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRFiniteEtaleAlgebra
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularRingIntegralClosure
import Nyll.SchemeTheory.RingTheory.Smooth.RegularBase
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Extending a generic cover on a smooth affine chart

Let `R` be a smooth domain over a DVR `B`, with prime special-fibre
parameter `p`. In residue characteristic zero, the normalization of `R`
in a finite separable function-field extension, étale after inverting
`p`, becomes finite étale after adjoining the factorial-degree root of
`p` on the actual chart.

The root chart is the original base change from the corresponding root
DVR over `B`. Its regularity, its domain property, the fraction fields,
and all local normalization comparisons are constructed. Primes away
from the root divisor are handled by the original étale cover. A
height-one prime containing the root is the root prime itself, where the
DVR normalization calculation applies. Purity supplies global étaleness
of each literal generic tensor component; the actual product comparison
then reconstructs the whole cover.

This is the affine prime-special-fibre extension step in Stacks Project,
Proposition 58.30.2: https://stacks.math.columbia.edu/tag/0C0Q.
Passing from these charts to an arbitrary smooth proper scheme and its
geometric generic covers is a separate step.
-/

noncomputable section

open Polynomial
open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

private theorem charZero_residueField_of_uniformizer
    (B V : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing V] [IsLocalRing V] [Algebra B V]
    [CharZero (IsLocalRing.ResidueField B)]
    (π : B) (hπ : Prime π)
    (hπV : algebraMap B V π ∈ IsLocalRing.maximalIdeal V) :
    CharZero (IsLocalRing.ResidueField V) := by
  let f : B →+* IsLocalRing.ResidueField V :=
    (IsLocalRing.residue V).comp (algebraMap B V)
  have hker : IsLocalRing.maximalIdeal B ≤ RingHom.ker f := by
    rw [hπ.irreducible.maximalIdeal_eq]
    apply Ideal.span_le.mpr
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hπV
  let fbar : IsLocalRing.ResidueField B →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal B) f hker
  exact charZero_of_injective_ringHom fbar.injective

/-- Over a smooth affine domain with prime special fibre, the actual
factorial root base change makes a finite separable generic cover,
initially étale off the special fibre, finite étale everywhere by its
literal normalization. The entire generic tensor product is recovered. -/
theorem finiteEtale_smoothPrimeFiberFactorial_normalization
    (B R L : Type u)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CharZero (IsLocalRing.ResidueField B)]
    [CommRing R] [IsDomain R] [Algebra B R] [Algebra.Smooth B R]
    (π : B) (hπ : Prime π) (hp : Prime (algebraMap B R π)) :
    let p := algebraMap B R π
    let P := Ideal.span ({p} : Set R)
    let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    let V := Localization.AtPrime P
    let K := FractionRing V
    ∀ [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
      [FiniteDimensional K L] [Algebra.IsSeparable K L],
      (Localization.awayMap (algebraMap R (integralClosure R L)) p).Etale →
      let n := (Module.finrank K L).factorial
      let D := AdjoinRoot (X ^ n - C p)
      let q := Ideal.span ({AdjoinRoot.root (X ^ n - C p)} : Set D)
      let : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
        (prime_adjoinRoot_root_of_prime (Nat.factorial_pos _) hp)
      let : q.LiesOver P := span_root_liesOver_span_radicand (Nat.factorial_pos _) hp
      let W := Localization.AtPrime q
      let : Algebra V W := Localization.AtPrime.algebraOfLiesOver P q
      let : IsRegularRing R := Algebra.Smooth.isRegularRing_of_isRegularRing B R
      let : IsDomain W :=
        adjoinRootLocalizationAtRootPrime_isDomain (Nat.factorial_pos _) hp
      let : IsDiscreteValuationRing W :=
        adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing (Nat.factorial_pos _) hp
      let Rn := AdjoinRoot (X ^ n - C (algebraMap R V p))
      let eLocal : Rn ≃ₐ[V] W :=
        adjoinRootLocalizationAtRootPrimeAlgEquiv (Nat.factorial_pos _) hp
      let : Module.Free V Rn :=
        (monic_X_pow_sub_C (algebraMap R V p) (Nat.factorial_pos _).ne').free_adjoinRoot
      let : Module.Free V W := Module.Free.of_equiv eLocal.toLinearEquiv
      let F := FractionRing W
      let : Algebra K F := FractionRing.liftAlgebra V F
      let G := F ⊗[K] L
      let : Algebra D G := genericTensorProductLeftScalarAlgebra
      Module.Finite D (integralClosure D G) ∧ Algebra.Etale D (integralClosure D G) ∧
        Nonempty (F ⊗[D] integralClosure D G ≃ₐ[F] G) := by
  intro p P hP V K hFieldL aKL aRL hRKL hFiniteL hSepL hAway
    n D q hq hqP W aVW hRegularR hDomainW hDvrW Rn eLocal hFreeRn hFreeW F aKF G aDG
  have : IsFractionRing R K := SchemeTheory.isFractionRing_of_localizationAtPrime P
  have : IsIntegrallyClosed R := SchemeTheory.isIntegrallyClosed_of_isRegularRing R
  have : IsDomain D :=
    isDomain_adjoinRoot_X_pow_sub_C_of_isIntegrallyClosed (Nat.factorial_pos _) hp
  have : IsRegularRing D := by
    let Bn := AdjoinRoot (X ^ n - C π)
    let : Algebra Bn D := rootBaseChangeRootAlgebra B R n π
    exact (uniformizerRoot_smoothBaseChange_regular B R n (Nat.factorial_pos _) π hπ).2.1
  have : IsIntegrallyClosed D := SchemeTheory.isIntegrallyClosed_of_isRegularRing D
  have : IsFractionRing D F := SchemeTheory.isFractionRing_of_localizationAtPrime q
  have : IsScalarTower V K F := FractionRing.isScalarTower_liftAlgebra V F
  have : IsScalarTower R V F := IsScalarTower.to₁₂₄ R V W F
  have : IsScalarTower R K F := IsScalarTower.to₁₃₄ R V K F
  have hCharZero : CharZero (V ⧸ IsLocalRing.maximalIdeal V) := by
    apply charZero_residueField_of_uniformizer B V π hπ
    change algebraMap R V p ∈ IsLocalRing.maximalIdeal V
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem (algebraMap R V) (Ideal.mem_span_singleton_self p)
  let C₀ := integralClosure R L
  have : Module.Finite R C₀ := IsIntegralClosure.finite R K L C₀
  have : IsFractionRing C₀ L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L C₀
  have : FaithfulSMul R C₀ := by
    apply (faithfulSMul_iff_algebraMap_injective R C₀).mpr
    have hinj : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    intro x y hxy
    exact hinj (congrArg (fun c : C₀ ↦ (c : L)) hxy)
  have hRootLocal :
      let : Algebra W G := genericTensorProductLeftScalarAlgebra
      Algebra.Etale W (integralClosure W G) := by
    let : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
    have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' rfl
    exact (finiteEtale_rootDivisorFactorial_normalization R p hp L hCharZero).2
  have hEtale : Algebra.Etale D (integralClosure D G) := by
    apply integralClosure_genericTensorProduct_etale
    intro m hm
    let M := GenericTensorFieldComponent m
    let : Algebra D M := genericTensorFieldComponentLeftScalarAlgebra m
    have : IsScalarTower D F M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hLocalAway (s : Ideal D) [s.IsPrime]
        (hsp : algebraMap R D p ∉ s) :
        Algebra.Etale (Localization.AtPrime s)
          (Localization (Algebra.algebraMapSubmonoid (integralClosure D M) s.primeCompl)) := by
      have hdisj : Disjoint ((Submonoid.powers (algebraMap R D p) : Submonoid D) : Set D)
          (s : Set D) := by
        rw [Set.disjoint_left]
        intro x hx hs
        obtain ⟨k, rfl⟩ := hx
        exact hsp ((inferInstance : s.IsPrime).mem_of_pow_mem k hs)
      exact localization_integralClosure_genericTensorFieldComponent_etale_of_awayMap
        (A := R) (C := C₀) (D := D) (F := K) (E := L) (K := F) p hp.ne_zero
        hAway s hdisj m
    have hLocalRoot : Algebra.Etale W
        (Localization (Algebra.algebraMapSubmonoid (integralClosure D M) q.primeCompl)) :=
      localization_integralClosure_genericTensorFieldComponent_etale_of_product
        D K F L q hRootLocal m
    let Z : Set (PrimeSpectrum D) := {s | algebraMap R D p ∈ s.asIdeal}
    apply SpecialLocalPurity.integralClosure_etale_of_regular_boundary (K := F) Z
    · intro s _
      exact inferInstance
    · intro Q hQ
      let s : PrimeSpectrum D := PrimeSpectrum.comap (algebraMap D (integralClosure D M)) Q
      exact SchemeTheory.isEtaleAt_of_localizedAlgebra_etale s
        (hLocalAway s.asIdeal hQ) Q rfl
    · intro s hs hsHeight Q hQ hQs
      let sPoint : PrimeSpectrum D := ⟨s, hs⟩
      let QPoint : PrimeSpectrum (integralClosure D M) := ⟨Q, hQ⟩
      have hUnder : PrimeSpectrum.comap (algebraMap D (integralClosure D M)) QPoint = sPoint :=
        PrimeSpectrum.ext (Q.over_def s).symm
      apply SchemeTheory.isEtaleAt_of_localizedAlgebra_etale sPoint _ QPoint hUnder
      by_cases hsp : algebraMap R D p ∈ s
      · have hRootMem : AdjoinRoot.root (X ^ n - C p) ∈ s := by
          apply (inferInstance : s.IsPrime).mem_of_pow_mem n
          rw [adjoinRoot_root_pow n p]
          exact hsp
        have hsq : s = q := s.eq_span_singleton_of_height_eq_one hsHeight hRootMem
          (prime_adjoinRoot_root_of_prime (Nat.factorial_pos _) hp)
        subst s
        exact hLocalRoot
      · exact hLocalAway s hsp
  have : Algebra.FinitePresentation D (integralClosure D G) := hEtale.finitePresentation
  have hFiniteType : Algebra.FiniteType D (integralClosure D G) :=
    Algebra.FiniteType.of_finitePresentation (R := D) (A := integralClosure D G)
  have hFinite : Module.Finite D (integralClosure D G) :=
    Algebra.IsIntegral.finite (R := D) (A := integralClosure D G) (h' := hFiniteType)
  have : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  have : Module.Finite F G := Module.Finite.base_change K F L
  have : Algebra.Etale F G := inferInstance
  have : IsScalarTower D F G :=
    TensorProduct.isScalarTower_left (R := K) (R'₂ := D) (R' := F)
  exact ⟨hFinite, hEtale, ⟨SchemeTheory.integralClosureFiniteEtaleGenericFiberEquiv D F G⟩⟩

end EtaleFundamentalGroups.Kummer
