/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RamificationInertia.Ramification
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryIntegralClosure
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain

/-!
# Tame prime data of the actual boundary normalization

At every maximal prime of the literal integral closure in a boundary-root
fraction field, the actual prime residue-field extension has degree one
and is separable, and the Dedekind ramification index is the root exponent.
The index is invertible in the residue field of the contracted prime.

The local normalization calculation in `BoundaryIntegralClosure` uses
residue fields of local rings and the length-based ramification index.
Here it is connected to the prime residue fields, their canonical localized
coefficient map, and the ideal-power ramification index used by the
codimension-one ramification criteria. No comparison map or residue
separability is assumed. This supplies the prime-wise local conditions for
Stacks Project, Example 58.31.4 (tag `0EYF`); it does not assert the
unconstructed arbitrary-cover scheme predicate.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The local-to-prime comparison is proved with abstract rings so that
residue-field localization never unfolds the boundary root construction. -/
private theorem localDvrPrimeData
    {R S : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.IsTorsionFree R S]
    {n : ℕ} (hnUnit : IsUnit (n : R))
    (hindexS : (IsLocalRing.maximalIdeal S).ramificationIdx R = n)
    (hresidueS : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R S)))
    (Q : Ideal S) [Q.IsMaximal] :
    let : Algebra (Q.under R).ResidueField Q.ResidueField :=
      (Ideal.ResidueField.map (Q.under R) Q (algebraMap R S) rfl).toAlgebra
    Function.Bijective (algebraMap (Q.under R).ResidueField Q.ResidueField) ∧
      Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧
      Module.finrank (Q.under R).ResidueField Q.ResidueField = 1 ∧
      Ideal.ramificationIdx' (Q.under R) Q = n ∧
      IsUnit (Ideal.ramificationIdx' (Q.under R) Q : (Q.under R).ResidueField) := by
  intro hresidueAlgebra
  have hQeq : Q = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal inferInstance
  subst Q
  let q := IsLocalRing.maximalIdeal S
  have hbase : q.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap (algebraMap R S)
  have hbijective : Function.Bijective
      (algebraMap (q.under R).ResidueField q.ResidueField) := by
    refine ⟨(algebraMap (q.under R).ResidueField q.ResidueField).injective, ?_⟩
    intro z
    obtain ⟨b, rfl⟩ := q.algebraMap_residueField_surjective z
    obtain ⟨a₀, ha₀⟩ := hresidueS.surjective (IsLocalRing.residue S b)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a₀
    refine ⟨algebraMap R (q.under R).ResidueField a, ?_⟩
    change Ideal.ResidueField.map (q.under R) q (algebraMap R S) rfl
      (algebraMap R (q.under R).ResidueField a) = _
    rw [Ideal.ResidueField.map_algebraMap]
    exact congrArg (algebraMap (S ⧸ q) q.ResidueField) ha₀
  have hseparable : Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hbijective.surjective x
    exact isSeparable_algebraMap a
  have hbaseNe : q.under R ≠ ⊥ := by
    rw [hbase]
    intro heq
    exact IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr heq)
  have hindex : Ideal.ramificationIdx' (q.under R) q = n :=
    (Ideal.ramificationIdx'_eq_ramificationIdx (R := R) (S := S)
      (q.under R) q hbaseNe).trans hindexS
  refine ⟨hbijective, hseparable, Module.finrank_of_bijective_algebraMap hbijective,
    hindex, ?_⟩
  rw [hindex]
  simpa only [map_natCast] using hnUnit.map (algebraMap R (q.under R).ResidueField)

/-- Every maximal prime of the literal normalization has trivial residue
extension and ramification index `n`, invertible in its base residue field.
The residue algebra is induced by the original coefficient map on the
actual prime localizations. -/
theorem standardKummerCover_boundaryTamePrimes
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : A)) :
    let V := Localization.AtPrime P
    let B := AdjoinRoot (X ^ n - C (algebraMap A V f))
    let : IsRegularLocalRing V :=
      SchemeTheory.isRegularLocalRing_localizationAtPrime_of_reduced_quotient f hf P hP
    let : IsDomain V := IsRegularLocalRing.isDomain V
    let : IsDiscreteValuationRing V :=
      SchemeTheory.isDiscreteValuationRing_localizationAtPrime_of_reduced_quotient f hf P hP
    ∃ hdomain : IsDomain B,
      let : IsDomain B := hdomain
      let : Module.FaithfullyFlat V B :=
        faithfullyFlat_adjoinRoot_X_pow_sub_C hn (algebraMap A V f)
      let N := integralClosure V (FractionRing B)
      ∀ (Q : Ideal N) [Q.IsMaximal],
        let : Algebra (Q.under V).ResidueField Q.ResidueField :=
          (Ideal.ResidueField.map (Q.under V) Q (algebraMap V N) rfl).toAlgebra
        Function.Bijective (algebraMap (Q.under V).ResidueField Q.ResidueField) ∧
          Algebra.IsSeparable (Q.under V).ResidueField Q.ResidueField ∧
          Module.finrank (Q.under V).ResidueField Q.ResidueField = 1 ∧
          Ideal.ramificationIdx' (Q.under V) Q = n ∧
          IsUnit (Ideal.ramificationIdx' (Q.under V) Q : (Q.under V).ResidueField) := by
  intro V B hregular hdomainV hdvrV
  obtain ⟨hdomainB, hnormalization⟩ :=
    standardKummerCover_boundaryIntegralClosure f hf P hP hn hnUnit
  refine ⟨hdomainB, ?_⟩
  intro hdomainB' hflat N Q hQ
  obtain ⟨hdvrN, hlocalN, hindexN, hresidueN, _hunitN⟩ := hnormalization
  have hnUnitV : IsUnit (n : V) := by
    simpa only [map_natCast] using hnUnit.map (algebraMap A V)
  exact localDvrPrimeData (R := V) (S := N) hnUnitV hindexN hresidueN Q

end EtaleFundamentalGroups.Kummer
