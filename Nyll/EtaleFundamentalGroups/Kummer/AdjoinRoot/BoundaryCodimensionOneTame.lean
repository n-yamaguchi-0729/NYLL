/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryStalkFieldFactors
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Ramification.TameDVR
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Standard root covers at every codimension-one boundary point

For a nonzerodivisor `f`, a boundary prime containing `f` and having a
one-dimensional actual scheme stalk is minimal over `(f)`. The proof
compares the stalk with the prime localization, then uses the positive
height of a nonzerodivisor and the minimal-prime height criterion.

This supplies the previously required minimal-prime input from the actual
codimension-one condition. The field-factor conclusion concerns the
literal finite-etale cover over `Spec A_f` and all maximal quotients of its
generic pullback at the scheme stalk.

This is the affine standard-root calculation in Stacks Project, Example
58.31.4 (tag `0EYF`). A global predicate for arbitrary schemes and transport
from an arbitrary dense open are not asserted here.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance] Ideal.Quotient.field

namespace EtaleFundamentalGroups.Kummer

/-- At a codimension-one point on a Cartier boundary, the prime is minimal
over its defining principal ideal. The dimension is that of the actual
scheme stalk, without a supplied minimal-prime or domain hypothesis. -/
theorem boundaryPrime_mem_minimalPrimes_of_stalkDimensionOne
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A) (x : PrimeSpectrum A)
    (hx : f ∈ x.asIdeal)
    (hdim : ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk x) = 1) :
    x.asIdeal ∈ (Ideal.span ({f} : Set A)).minimalPrimes := by
  let e : (Spec (CommRingCat.of A)).presheaf.stalk x ≃+*
      Localization.AtPrime x.asIdeal :=
    (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv
  have hdimLocal : ringKrullDim (Localization.AtPrime x.asIdeal) = 1 :=
    (ringKrullDim_eq_of_ringEquiv e).symm.trans hdim
  have hheight : x.asIdeal.height = 1 := by
    apply WithBot.coe_eq_coe.mp
    exact (IsLocalization.AtPrime.ringKrullDim_eq_height
      x.asIdeal (Localization.AtPrime x.asIdeal)).symm.trans hdimLocal
  apply Ideal.mem_minimalPrimes_of_height_le
    ((x.asIdeal.span_singleton_le_iff_mem).mpr hx)
  rw [hheight]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hf

/-- At every actual codimension-one point of the reduced Cartier boundary,
each literal field factor of the generic pullback of the original standard
root cover is finite separable of degree `n` and tame over that same stalk.
Minimality of the boundary prime is derived from `hx` and `hdim`. -/
theorem standardKummerCover_codimensionOneBoundary_allFieldFactors_tame
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (x : PrimeSpectrum A) (hx : f ∈ x.asIdeal)
    (hdim : ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk x) = 1)
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : A)) :
    let hP : x.asIdeal ∈ (Ideal.span ({f} : Set A)).minimalPrimes :=
      boundaryPrime_mem_minimalPrimes_of_stalkDimensionOne f hf x hx hdim
    let R : CommRingCat.{u} := (Spec (CommRingCat.of A)).presheaf.stalk x
    let V := Localization.AtPrime x.asIdeal
    let XAway : FiniteEtale (Spec (CommRingCat.of (Localization.Away f))) :=
      standardKummerAwayCover hn hnUnit f
    let : IsRegularLocalRing V :=
      SchemeTheory.isRegularLocalRing_localizationAtPrime_of_reduced_quotient
        f hf x.asIdeal hP
    let : IsDomain V := IsRegularLocalRing.isDomain V
    let : IsDiscreteValuationRing V :=
      SchemeTheory.isDiscreteValuationRing_localizationAtPrime_of_reduced_quotient
        f hf x.asIdeal hP
    let eStalk : R ≃+* V := (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv
    let : IsDomain R := eStalk.toMulEquiv.isDomain V
    let : IsDiscreteValuationRing R :=
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eStalk.symm
    ∃ r : Localization.Away f →+* FractionRing R,
      Spec.map (CommRingCat.ofHom r) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
          (Spec (CommRingCat.of A)).fromSpecStalk x ∧
      let Y : FiniteEtale (Spec (CommRingCat.of (FractionRing R))) :=
        (FiniteEtale.pullback (Spec.map (CommRingCat.ofHom r))).obj XAway
      let G : CommAlgCat.FiniteEtale.{u} (FractionRing R) :=
        (FiniteEtale.affineEquivalence (CommRingCat.of (FractionRing R))).functor.obj
          (Opposite.op Y)
      let : Algebra R G := Algebra.compHom G (algebraMap R (FractionRing R))
      ∀ m : MaximalSpectrum G,
        Module.Finite (FractionRing R) (G ⧸ m.asIdeal) ∧
          Algebra.IsSeparable (FractionRing R) (G ⧸ m.asIdeal) ∧
          Module.finrank (FractionRing R) (G ⧸ m.asIdeal) = n ∧
          SchemeTheory.IsTamelyRamifiedOverDVR R (G ⧸ m.asIdeal) := by
  intro hP R V XAway hregular hdomainV hdvrV eStalk hdomainR hdvrR
  exact standardKummerCover_boundaryStalk_allFieldFactors_tame
    f hf x.asIdeal hP hn hnUnit

end EtaleFundamentalGroups.Kummer
