/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryCodimensionOneTame
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryStalkFieldFactors
import Nyll.EtaleFundamentalGroups.Purity.CodimensionOneBoundary
import Nyll.EtaleFundamentalGroups.Purity.CodimensionOneGenericFiber
import Nyll.SchemeTheory.Divisors.ConnectedComplement
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.LocalGeometry.PuncturedDVR
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Ramification.TameDVR
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Closure

/-!
# The actual Cartier-boundary stalk square for the standard root cover

The commuting map from the boundary-stalk fraction field to `Spec A_f`
is cartesian over the original ambient spectrum. The proof uses the
existing description of the inverse image of a dense open at a
codimension-one point as the punctured stalk, and the existing description
of the puncture of a DVR as its fraction-field spectrum.

After the canonical `D(f)` / `Spec A_f` identification, the map is exactly
the generic-point map already used by the codimension-one purity API. Thus
the field factors whose tameness was computed for the standard root cover
are formed using the original cartesian stalk square in Stacks Project,
Section 58.31 (tag `0BSE`), rather than only a commuting square.
https://stacks.math.columbia.edu/tag/0BSE
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

attribute [local instance] Ideal.Quotient.field

namespace EtaleFundamentalGroups.Kummer

/-- A map over the ambient affine scheme to the Cartier complement gives
the actual stalk pullback square when the boundary stalk is a DVR. -/
private theorem boundaryFractionFieldMap_isPullback
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (x : PrimeSpectrum A) (hx : f ∈ x.asIdeal)
    (hdim : ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk x) = 1)
    [IsDomain ((Spec (CommRingCat.of A)).presheaf.stalk x)]
    [IsDiscreteValuationRing ((Spec (CommRingCat.of A)).presheaf.stalk x)]
    (r : Localization.Away f →+* FractionRing ((Spec (CommRingCat.of A)).presheaf.stalk x))
    (hr : Spec.map (CommRingCat.ofHom r) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) =
      Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of A)).presheaf.stalk x)
        (FractionRing ((Spec (CommRingCat.of A)).presheaf.stalk x)))) ≫
          (Spec (CommRingCat.of A)).fromSpecStalk x) :
    IsPullback (Spec.map (CommRingCat.ofHom r))
      (Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of A)).presheaf.stalk x)
        (FractionRing ((Spec (CommRingCat.of A)).presheaf.stalk x)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))
      ((Spec (CommRingCat.of A)).fromSpecStalk x) := by
  let R : CommRingCat.{u} := (Spec (CommRingCat.of A)).presheaf.stalk x
  let U : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen f
  have hU : Dense (U : Set (Spec (CommRingCat.of A))) :=
    PrimeSpectrum.dense_basicOpen_of_isRegular (isRegular_iff_mem_nonZeroDivisors.mpr hf)
  have hxU : x ∉ U := fun hmem => (show f ∉ x.asIdeal from hmem) hx
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R)))) :=
    Scheme.isOpenImmersion_SpecMap_fractionField_of_dvr R (FractionRing R)
  have hrange : (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R)))).opensRange = Scheme.puncturedSpectrumOpen R := by
    apply Opens.ext
    exact Scheme.range_SpecMap_fractionField_of_dvr R (FractionRing R)
  apply IsOpenImmersion.isPullback
  · exact hr.symm
  · rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) f, hrange]
    exact Scheme.fromSpecStalk_preimage_dense_open_eq_puncturedSpectrumOpen
      U hU x hxU hdim

/-- For the original standard Kummer cover, the canonical cartesian
boundary-stalk square and every tame generic field factor occur with the
same fraction-field map and the same affine finite-etale algebra. -/
theorem standardKummerCover_codimensionOneBoundary_cartesian_and_tame
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
    let U : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen f
    let hU : Dense (U : Set (Spec (CommRingCat.of A))) :=
      PrimeSpectrum.dense_basicOpen_of_isRegular (isRegular_iff_mem_nonZeroDivisors.mpr hf)
    let hxU : x ∉ U := fun hmem => (show f ∉ x.asIdeal from hmem) hx
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
          (basicOpenIsoSpecAway (R := CommRingCat.of A) f).inv =
        Scheme.denseOpenDVRFractionFieldMap U hU x hxU hdim ∧
      IsPullback (Spec.map (CommRingCat.ofHom r))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))
        ((Spec (CommRingCat.of A)).fromSpecStalk x) ∧
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
  intro hP R V U hU hxU XAway hregular hdomainV hdvrV eStalk hdomainR hdvrR
  obtain ⟨r, hr, hfieldFactors⟩ :=
    standardKummerCover_codimensionOneBoundary_allFieldFactors_tame f hf x hx hdim hn hnUnit
  refine ⟨r, ?_, boundaryFractionFieldMap_isPullback f hf x hx hdim r hr, hfieldFactors⟩
  have hbasic : (basicOpenIsoSpecAway (R := CommRingCat.of A) f).inv ≫ U.ι =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) :=
    (Iso.inv_comp_eq (basicOpenIsoSpecAway (R := CommRingCat.of A) f)).mpr
      (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) f).symm
  have hcanonical := Scheme.denseOpenDVRFractionFieldMap_comp_ι
    (X := Spec (CommRingCat.of A)) U hU
    (show Spec (CommRingCat.of A) from x) hxU hdim
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, hbasic]
  exact hr.trans hcanonical.symm

end EtaleFundamentalGroups.Kummer
