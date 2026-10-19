/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.ChosenFractionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.GaloisChosenFractionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.WholeRelativeNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.LocalizationAtRootPrime
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.NormalDomainRoot
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.SmoothBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.SmoothRootNormalization
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.StandardCompletion
import Nyll.SchemeTheory.Normalization.IntegralOpen
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.PrimeFractionRing
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularRingIntegralClosure
import Nyll.SchemeTheory.RingTheory.Smooth.RegularBase
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The original Galois cover on a characteristic-zero smooth chart

Over a DVR with residue characteristic zero, a finite étale Galois cover
on a smooth prime-fibre affine chart extends after adjoining a root of
the factorial of its automorphism-group order. The extension is the
relative normalization of the actual original base-changed cover, and
its restriction recovers that same original cover.

The given cover supplies the function field, its finite separable
extension, its degree, and étaleness away from the parameter. Its actual
coefficient action is retained in the local normalization calculation.
The whole tensor product is used, including every component created by
the ramified base change.

This is the affine extension step of Stacks Project 58.30.2,
https://stacks.math.columbia.edu/tag/0C0Q. Passing to a whole smooth scheme
and then descending arbitrary geometric generic covers are further steps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

namespace EtaleFundamentalGroups

open Kummer

universe u

/-- The factorial of the original Galois order is an explicit root
exponent making the actual chart normalization finite étale in residue
characteristic zero. Its generic-open restriction is the original cover. -/
theorem exists_finiteEtale_smoothPrimeFiberCharacteristicZeroCover_normalization
    (B R : Type u)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CharZero (IsLocalRing.ResidueField B)]
    [CommRing R] [IsDomain R] [Algebra B R] [Algebra.Smooth B R]
    (π : B) (hπ : Prime π) (hp : Prime (algebraMap B R π)) :
    let : IsRegularRing R := Algebra.Smooth.isRegularRing_of_isRegularRing B R
    let : IsIntegrallyClosed R := SchemeTheory.isIntegrallyClosed_of_isRegularRing R
    let p := algebraMap B R π
    let S := Localization.Away p
    let : IsDomain S := IsLocalization.Away.isDomain S hp.ne_zero
    let : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers p)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero))
    ∀ (Y : FiniteEtale (Spec (.of S))) [PreGaloisCategory.IsGalois Y],
      ∃ n : ℕ, n = (Nat.card (Aut Y)).factorial ∧ 0 < n ∧
        let D : Type u := AdjoinRoot (X ^ n - C p)
        let S' : Type u := Localization.Away (AdjoinRoot.of (X ^ n - C p) p)
        let : Algebra S S' :=
          (Localization.awayMap (AdjoinRoot.of (X ^ n - C p)) p).toAlgebra
        let y : Y.left ⟶ Spec (.of S) := Y.hom
        let b := Spec.map (CommRingCat.ofHom (algebraMap S S'))
        let j := Spec.map (CommRingCat.ofHom (algebraMap D S'))
        let g := pullback.snd y b ≫ j
        let : IsFinite y := Y.prop.toIsFinite
        let : QuasiCompact g := inferInstance
        let : QuasiSeparated g := inferInstance
        IsFiniteEtale g.fromNormalization ∧
          ∃ e : pullback g.fromNormalization j ≅ pullback y b,
            e.hom ≫ pullback.snd y b = pullback.snd g.fromNormalization j := by
  intro hRegularR hNormalR p S hDomainS hNormalS Y hGaloisY
  let P := Ideal.span ({p} : Set R)
  have : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let V := Localization.AtPrime P
  let K := FractionRing V
  have : IsFractionRing R K := SchemeTheory.isFractionRing_of_localizationAtPrime P
  have : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let L := Y.left.functionField
  let : Algebra K L := finiteEtaleAwayChosenFractionFieldAlgebra (K := K) p hp.ne_zero Y
  let : Algebra R L := finiteEtaleAwayFunctionFieldAlgebra p hp.ne_zero Y
  have hField := finiteEtaleAwayChosenFractionField_finite_separable (K := K) p hp.ne_zero Y
  have : IsScalarTower R K L := hField.1
  have : FiniteDimensional K L := hField.2.1
  have : Algebra.IsSeparable K L := hField.2.2
  have hGalois := finiteEtaleAwayChosenFractionField_galois_degree (K := K) p hp.ne_zero Y
  have hAway : (Localization.awayMap (algebraMap R (integralClosure R L)) p).Etale :=
    localization_away_integralClosure_functionField_etale_of_finiteEtale p hp.ne_zero Y
  let n := (Module.finrank K L).factorial
  have hn : 0 < n := Nat.factorial_pos _
  refine ⟨n, congrArg Nat.factorial hGalois.2.symm, hn, ?_⟩
  intro D S' aSS' y b j g hFiniteY hQcG hQsG
  let q := Ideal.span ({AdjoinRoot.root (X ^ n - C p)} : Set D)
  have : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
    (prime_adjoinRoot_root_of_prime hn hp)
  have : q.LiesOver P := span_root_liesOver_span_radicand hn hp
  let W := Localization.AtPrime q
  let : Algebra V W := Localization.AtPrime.algebraOfLiesOver P q
  have : IsDomain W := adjoinRootLocalizationAtRootPrime_isDomain hn hp
  have : IsDiscreteValuationRing W :=
    adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing hn hp
  let Rn := AdjoinRoot (X ^ n - C (algebraMap R V p))
  let eLocal : Rn ≃ₐ[V] W := adjoinRootLocalizationAtRootPrimeAlgEquiv hn hp
  have : Module.Free V Rn := (monic_X_pow_sub_C (algebraMap R V p) hn.ne').free_adjoinRoot
  have : Module.Free V W := Module.Free.of_equiv eLocal.toLinearEquiv
  let F := FractionRing W
  let : Algebra K F := FractionRing.liftAlgebra V F
  let G := F ⊗[K] L
  let : Algebra D G := genericTensorProductLeftScalarAlgebra
  have hNormalization : Module.Finite D (integralClosure D G) ∧
      Algebra.Etale D (integralClosure D G) ∧
      Nonempty (F ⊗[D] integralClosure D G ≃ₐ[F] G) :=
    finiteEtale_smoothPrimeFiberFactorial_normalization B R L π hπ hp hAway
  have : IsDomain D := isDomain_adjoinRoot_X_pow_sub_C_of_isIntegrallyClosed hn hp
  have : IsRegularRing D := by
    let Bn := AdjoinRoot (X ^ n - C π)
    let : Algebra Bn D := rootBaseChangeRootAlgebra B R n π
    exact (uniformizerRoot_smoothBaseChange_regular B R n hn π hπ).2.1
  have : IsIntegrallyClosed D := SchemeTheory.isIntegrallyClosed_of_isRegularRing D
  have : IsFractionRing D F := SchemeTheory.isFractionRing_of_localizationAtPrime q
  have : IsScalarTower V K F := FractionRing.isScalarTower_liftAlgebra V F
  have : IsScalarTower R V F := IsScalarTower.to₁₂₄ R V W F
  have : IsScalarTower R K F := IsScalarTower.to₁₃₄ R V K F
  obtain ⟨e, he⟩ := exists_wholeRelativeNormalizationIso
    (R := R) (D := D) (K := K) (F := F) p hp.ne_zero Y
  let t : Spec (.of (integralClosure D G)) ⟶ Spec (.of D) :=
    Spec.map (CommRingCat.ofHom (R := D) (S := integralClosure D G)
      (algebraMap D (integralClosure D G)))
  have hFiniteT : IsFinite t :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hNormalization.1)
  have hEtaleT : Etale t := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr hNormalization.2.1)
  have heOriginal : e.hom ≫ t = g.fromNormalization := he
  have hLocality : IsZariskiLocalAtTarget
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance).1
  have hRespects : MorphismProperty.RespectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := hLocality.toRespects
  have ht : IsFiniteEtale t := @IsFiniteEtale.mk _ _ _ hFiniteT hEtaleT
  have hFiniteEtale : IsFiniteEtale g.fromNormalization :=
    heOriginal ▸ (MorphismProperty.cancel_left_of_respectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) e.hom t).mpr ht
  refine ⟨hFiniteEtale, ?_⟩
  let eOpen := Scheme.Hom.integralOpenNormalizationIso (pullback.snd y b) j
  refine ⟨eOpen.symm, ?_⟩
  change eOpen.inv ≫ pullback.snd y b = pullback.snd g.fromNormalization j
  have hOpen : eOpen.hom ≫ pullback.snd g.fromNormalization j = pullback.snd y b :=
    Scheme.Hom.integralOpenNormalizationIso_hom_snd (pullback.snd y b) j
  exact (congrArg (fun k => eOpen.inv ≫ k) hOpen).symm.trans
    (eOpen.inv_hom_id_assoc (pullback.snd g.fromNormalization j))

end EtaleFundamentalGroups
