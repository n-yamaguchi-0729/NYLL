/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryTamePrimes
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.SchemeTheory.RingTheory.Ramification.TameDVR
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain

/-!
# Tameness of the actual boundary generic fibre of a standard root cover

The generic pullback of the literal away-cover is the spectrum of a finite
separable field extension, and that same extension is tamely ramified with
respect to the original boundary DVR. The comparison preserves its
projection to the base fraction field and the original coefficients.

The field and its comparison are constructed by `BoundaryGenericFiber`.
The finite separability comes from `UniformizerGenericFiber`, while the
prime conditions on its literal integral closure come from
`BoundaryTamePrimes`. No unrelated extension field or assumed comparison
is substituted for the generic fibre of the original scheme morphism.

This verifies the field-extension condition at each minimal prime of the
reduced Cartier boundary in Stacks Project, Example 58.31.4 (tag `0EYF`).
The arbitrary-scheme codimension-one predicate and its affine-stalk
comparison are separate from this statement.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial AlgebraicGeometry CategoryTheory Limits

universe u

/-- The original away-cover's generic fibre at a boundary prime is a
finite separable, tamely ramified extension of degree `n`, with the
comparison over the actual base fraction field. -/
theorem standardKummerCover_tameBoundaryGenericFiber
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : A)) :
    let V := Localization.AtPrime P
    let C₀ := AdjoinRoot (X ^ n - C f)
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
      let : Algebra (FractionRing V) (FractionRing B) :=
        FractionRing.liftAlgebra V (FractionRing B)
      Module.Finite (FractionRing V) (FractionRing B) ∧
        Algebra.IsSeparable (FractionRing V) (FractionRing B) ∧
        Module.finrank (FractionRing V) (FractionRing B) = n ∧
        SchemeTheory.IsTamelyRamifiedOverDVR V (FractionRing B) ∧
        ∃ r : Localization.Away f →+* FractionRing V,
          r.comp (algebraMap A (Localization.Away f)) =
            (algebraMap V (FractionRing V)).comp (algebraMap A V) ∧
          ∃ e : Spec (CommRingCat.of (FractionRing B)) ≅
              pullback
                (Spec.map (CommRingCat.ofHom
                  (Localization.awayMap (algebraMap A C₀) f)))
                (Spec.map (CommRingCat.ofHom r)),
            e.hom ≫ pullback.snd _ _ =
              Spec.map (CommRingCat.ofHom
                (algebraMap (FractionRing V) (FractionRing B))) := by
  intro V C₀ B hregular hdomainV hdvrV
  obtain ⟨hdomainB, hgeneric⟩ :=
    standardKummerCover_boundaryGenericFiber f hf P hP hn
  refine ⟨hdomainB, ?_⟩
  intro hdomainB' hflat hfieldAlgebra
  let π : V := algebraMap A V f
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span ({π} : Set V) :=
    SchemeTheory.maximalIdeal_localizationAtPrime_eq_span_of_reduced_quotient f P hP
  have hπ : Prime π :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hmax).prime
  have hnUnitV : IsUnit (n : V) := by
    simpa only [map_natCast] using hnUnit.map (algebraMap A V)
  obtain ⟨hfinite, hseparable, hdegree⟩ :=
    uniformizerRoot_fractionField_finiteSeparable_degree hn hnUnitV π hπ
  refine ⟨hfinite, hseparable, hdegree, ?_, hgeneric⟩
  obtain ⟨_hdomain, hprimes⟩ :=
    standardKummerCover_boundaryTamePrimes f hf P hP hn hnUnit
  apply Or.inr
  intro Q hQ hresidueAlgebra
  have hdata := hprimes Q
  exact ⟨hdata.2.1, hdata.2.2.2.2⟩

end EtaleFundamentalGroups.Kummer
