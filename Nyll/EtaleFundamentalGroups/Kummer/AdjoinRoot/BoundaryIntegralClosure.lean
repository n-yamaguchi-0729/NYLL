/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RamificationInertia.Ramification
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.ReducedBoundary
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Ramification.BaseChange.Equiv
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain

/-!
# The literal integral closure at a reduced Kummer boundary

The integral closure of the actual boundary DVR in the fraction field of
its integral root algebra is itself a DVR. Its ramification index is the
original exponent, and its actual residue map is bijective. When that
exponent is invertible in the original base, the index is invertible in
the base residue field.

`ReducedBoundary` supplies the integral root algebra and its ramification
calculation. The comparison with the literal `integralClosure` is Mathlib's
`IsIntegralClosure.equiv`; it is not redefined here. The existing algebra
equivalence and residue-field functor transport the original calculation.
The ambient fraction field is the same one identified with the actual
away-cover generic fiber in `BoundaryGenericFiber`.

This is the normalization calculation for Stacks Project, Example 58.31.4
(tag `0EYF`): https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The literal normalization in the original root algebra's fraction field
is a DVR with ramification index `n` and trivial residue extension. The
DVR and locality of the coefficient map are constructed, not assumed. -/
theorem standardKummerCover_boundaryIntegralClosure
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
      ∃ hdvr : IsDiscreteValuationRing N,
        let : IsDiscreteValuationRing N := hdvr
        ∃ hlocal : IsLocalHom (algebraMap V N),
          let : IsLocalHom (algebraMap V N) := hlocal
          (IsLocalRing.maximalIdeal N).ramificationIdx V = n ∧
            Function.Bijective (IsLocalRing.ResidueField.map (algebraMap V N)) ∧
            IsUnit ((IsLocalRing.maximalIdeal N).ramificationIdx V :
              IsLocalRing.ResidueField V) := by
  intro V B hregular hdomainV hdvrV
  obtain ⟨hdomainB, hboundary⟩ :=
    standardKummerCover_reducedBoundary f hf P hP hn hnUnit
  refine ⟨hdomainB, ?_⟩
  intro hdomainB' hflat N
  obtain ⟨hdvrB, hnormal, hindexB, hresidueB, hunitB⟩ := hboundary
  let e : B ≃ₐ[V] N :=
    IsIntegralClosure.equiv V B (FractionRing B) N
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_⟩
  intro hdvrN
  have : IsLocalHom e.toRingEquiv.toRingHom := isLocalHom_toRingHom e.toRingEquiv
  have hbase : e.toRingEquiv.toRingHom.comp (algebraMap V B) = algebraMap V N :=
    RingHom.ext e.commutes
  have hlocal : IsLocalHom (algebraMap V N) := by
    rw [← hbase]
    infer_instance
  refine ⟨hlocal, ?_⟩
  intro hlocalN
  have hindex : (IsLocalRing.maximalIdeal N).ramificationIdx V =
      (IsLocalRing.maximalIdeal B).ramificationIdx V := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv]
    exact ramificationIdx_map_eq_of_algEquiv e (IsLocalRing.maximalIdeal B)
  refine ⟨hindex.trans hindexB, ?_, ?_⟩
  · have hresidue :=
      (IsLocalRing.ResidueField.mapEquiv e.toRingEquiv).bijective.comp hresidueB
    change Function.Bijective
      ((IsLocalRing.ResidueField.map e.toRingEquiv.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap V B))) at hresidue
    rw [← IsLocalRing.ResidueField.map_comp] at hresidue
    simpa only [hbase] using hresidue
  · rw [hindex]
    exact hunitB

end EtaleFundamentalGroups.Kummer
