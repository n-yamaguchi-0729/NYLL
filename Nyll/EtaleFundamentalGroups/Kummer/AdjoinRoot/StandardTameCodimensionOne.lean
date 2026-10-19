/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryCodimensionOneTame
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryStalkCartesian
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryStalkFieldFactors
import Nyll.EtaleFundamentalGroups.Purity.CodimensionOneGenericFiber
import Nyll.EtaleFundamentalGroups.Purity.TameCodimensionOne
import Nyll.SchemeTheory.Divisors.ConnectedComplement
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Ramification.TameDVR
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Closure

/-!
# Standard Kummer covers are tame along their Cartier boundary

This is the codimension-one tame assertion of Stacks Project, Example
58.31.4 (0EYF), for the actual standard cover restricted to the actual
basic open D(f). The previous Cartesian comparison identifies the
fraction-field map used in the standard-root calculation with the
canonical map appearing in the scheme-level definition of tameness.

Functorial composition of actual finite-etale pullbacks then identifies
the two generic covers. The induced coordinate-algebra and maximal-quotient
comparisons transport the already proved tame extensions. No field-factor,
ramification or generic-fiber comparison is added as an assumption.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

attribute [local instance] Ideal.Quotient.field
  FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

namespace EtaleFundamentalGroups.Kummer

/-- The standard root cover, viewed on the actual Cartier complement D(f),
satisfies the original scheme-level codimension-one tame condition. -/
theorem standardKummerCover_isTamelyRamifiedInCodimensionOne
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : A)) :
    let U : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen f
    let hU : Dense (U : Set (Spec (CommRingCat.of A))) :=
      PrimeSpectrum.dense_basicOpen_of_isRegular (isRegular_iff_mem_nonZeroDivisors.mpr hf)
    FiniteEtale.IsTamelyRamifiedInCodimensionOne U hU
      ((FiniteEtale.pullback (basicOpenIsoSpecAway (R := CommRingCat.of A) f).hom).obj
        (standardKummerAwayCover hn hnUnit f)) := by
  intro U hU x hx hdim
  let P : PrimeSpectrum A := x
  have hxP : f ∈ P.asIdeal := by
    by_contra h
    exact hx (show x ∈ U from h)
  let hP : P.asIdeal ∈ (Ideal.span ({f} : Set A)).minimalPrimes :=
    boundaryPrime_mem_minimalPrimes_of_stalkDimensionOne f hf P hxP hdim
  let R : CommRingCat.{u} := (Spec (CommRingCat.of A)).presheaf.stalk x
  let V := Localization.AtPrime P.asIdeal
  let hregular : IsRegularLocalRing V :=
    SchemeTheory.isRegularLocalRing_localizationAtPrime_of_reduced_quotient
      f hf P.asIdeal hP
  let hdomainV : IsDomain V := IsRegularLocalRing.isDomain V
  let hdvrV : IsDiscreteValuationRing V :=
    SchemeTheory.isDiscreteValuationRing_localizationAtPrime_of_reduced_quotient
      f hf P.asIdeal hP
  let eStalk : R ≃+* V := (Spec.stalkIso (CommRingCat.of A) P).commRingCatIsoToRingEquiv
  let hdomainR : IsDomain R := eStalk.toMulEquiv.isDomain V
  let hdvrR : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eStalk.symm
  refine ⟨hdomainR, ?_⟩
  intro hdomain
  refine ⟨hdvrR, ?_⟩
  intro hdvr K rU G hRG
  let XAway : FiniteEtale (Spec (CommRingCat.of (Localization.Away f))) :=
    standardKummerAwayCover hn hnUnit f
  let eOpen : U.toScheme ≅ Spec (CommRingCat.of (Localization.Away f)) :=
    basicOpenIsoSpecAway (R := CommRingCat.of A) f
  obtain ⟨r, hr, _, hfields⟩ :=
    standardKummerCover_codimensionOneBoundary_cartesian_and_tame f hf P hxP hdim hn hnUnit
  have hgeneric : rU ≫ eOpen.hom = Spec.map (CommRingCat.ofHom r) := by
    calc
      rU ≫ eOpen.hom = (Spec.map (CommRingCat.ofHom r) ≫ eOpen.inv) ≫ eOpen.hom :=
        congrArg (fun t : Spec (CommRingCat.of K) ⟶ U.toScheme => t ≫ eOpen.hom) hr.symm
      _ = Spec.map (CommRingCat.ofHom r) := by
        rw [Category.assoc, eOpen.inv_hom_id, Category.comp_id]
  let c : FiniteEtale.pullback (Spec.map (CommRingCat.ofHom r)) ≅
      FiniteEtale.pullback eOpen.hom ⋙ FiniteEtale.pullback rU :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      rU eOpen.hom (Spec.map (CommRingCat.ofHom r)) hgeneric.symm
  let YOld : FiniteEtale (Spec (CommRingCat.of K)) :=
    (FiniteEtale.pullback (Spec.map (CommRingCat.ofHom r))).obj XAway
  let YNew : FiniteEtale (Spec (CommRingCat.of K)) :=
    (FiniteEtale.pullback rU).obj ((FiniteEtale.pullback eOpen.hom).obj XAway)
  have hOld :
      let B : CommAlgCat.FiniteEtale.{u} K :=
        (FiniteEtale.affineEquivalence (CommRingCat.of K)).functor.obj (Opposite.op YOld)
      let : Algebra R B := Algebra.compHom B (algebraMap R K)
      ∀ m : MaximalSpectrum B, SchemeTheory.IsTamelyRamifiedOverDVR R (B ⧸ m.asIdeal) := by
    intro B hRB m
    exact (hfields m).2.2.2
  exact FiniteEtale.tame_field_factors_of_iso R K YOld YNew (c.app XAway) hOld

end EtaleFundamentalGroups.Kummer
