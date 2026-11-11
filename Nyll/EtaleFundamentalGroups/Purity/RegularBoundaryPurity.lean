/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.RegularBoundaryExtension
public import Nyll.EtaleFundamentalGroups.Purity.RegularBoundaryFullyFaithful
public import Nyll.EtaleFundamentalGroups.Purity.CodimensionOneGenericFiber
public import Nyll.SchemeTheory.Divisors.ConnectedComplement
public import Nyll.SchemeTheory.Divisors.RegularCartier
public import Nyll.SchemeTheory.Divisors.LocalComplement
public import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
public import Nyll.SchemeTheory.FiniteEtale.LocalExtensionGluing
public import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRNormalization
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDimensionOne
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Regular-boundary purity on locally Noetherian schemes

Every point has an extension neighborhood containing the entire original
open. Full faithfulness identifies these actual extensions on all overlaps;
effective finite etale gluing constructs the global extension. No global
Noetherianity or Cartier hypothesis is imposed in the general theorem.

A regular effective Cartier divisor supplies boundary regularity by the
actual regular-quotient theorem, giving the original divisor specialization.

References: Stacks Project, Tags 0H2W and 0EYE.
https://stacks.math.columbia.edu/tag/0H2W
https://stacks.math.columbia.edu/tag/0EYE
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] Ideal.Quotient.field

/-- A finite etale cover of a dense open extends over a locally Noetherian
scheme when the boundary is regular and the literal field factors at each
codimension-one missing point are unramified over its DVR stalk. -/
theorem exists_extension_of_regular_boundary_of_unramified_codimensionOne_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (Y : FiniteEtale U.toScheme)
    (hunramified : ∀ (x : X) (hx : x ∉ U)
      (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)),
      let R : CommRingCat.{u} := X.presheaf.stalk x
      let : IsRegularLocalRing R := hregular x hx
      let : IsDomain R := IsRegularLocalRing.isDomain R
      let : IsDiscreteValuationRing R :=
        SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one R hdim
      let K : Type u := FractionRing R
      let r : Spec (.of K) ⟶ U.toScheme :=
        Scheme.denseOpenDVRFractionFieldMap U hU x hx hdim
      let A : CommAlgCat.FiniteEtale.{u} K :=
        (affineEquivalence (.of K)).functor.obj (Opposite.op ((pullback r).obj Y))
      let : Algebra R A := Algebra.compHom A (algebraMap R K)
      ∀ m : MaximalSpectrum A, SchemeTheory.IsUnramifiedOverDVR R (A ⧸ m.asIdeal)) :
    ∃ Z : FiniteEtale X, Nonempty ((pullback U.ι).obj Z ≅ Y) := by
  exact exists_extension_of_locally_exists_of_restriction_fullyFaithful U Y
    (denseOpenHomOfLEPullbackFullyFaithful_of_regular_boundary U hU hregular)
    (exists_open_extension_containing_point_of_regular_boundary U hU hregular Y hunramified)

/-- A finite etale cover unramified in codimension one extends across an
effective Cartier divisor whose closed subscheme is regular. -/
theorem exists_extension_of_regular_cartier_divisor_of_unramified_codimensionOne
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor)
    (hregularD : ∀ z : D.1.subscheme,
      IsRegularLocalRing (D.1.subscheme.presheaf.stalk z))
    (Y : FiniteEtale D.1.supportComplement.toScheme)
    (hunramified : ∀ (x : X) (hx : x ∉ D.1.supportComplement)
      (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)),
      let R : CommRingCat.{u} := X.presheaf.stalk x
      let : IsRegularLocalRing R :=
        D.2.isAmbientRegularAlongSupport_of_regular_subscheme hregularD x (not_not.mp hx)
      let : IsDomain R := IsRegularLocalRing.isDomain R
      let : IsDiscreteValuationRing R :=
        SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one R hdim
      let K : Type u := FractionRing R
      let r : Spec (.of K) ⟶ D.1.supportComplement.toScheme :=
        Scheme.denseOpenDVRFractionFieldMap D.1.supportComplement D.dense_supportComplement
          x hx hdim
      let A : CommAlgCat.FiniteEtale.{u} K :=
        (affineEquivalence (.of K)).functor.obj (Opposite.op ((pullback r).obj Y))
      let : Algebra R A := Algebra.compHom A (algebraMap R K)
      ∀ m : MaximalSpectrum A, SchemeTheory.IsUnramifiedOverDVR R (A ⧸ m.asIdeal)) :
    ∃ Z : FiniteEtale X, Nonempty ((pullback D.1.supportComplement.ι).obj Z ≅ Y) := by
  have hregular : ∀ (x : X), x ∉ D.1.supportComplement →
      IsRegularLocalRing (X.presheaf.stalk x) := by
    intro x hx
    exact D.2.isAmbientRegularAlongSupport_of_regular_subscheme hregularD x (not_not.mp hx)
  exact exists_extension_of_regular_boundary_of_unramified_codimensionOne_of_isLocallyNoetherian
    D.1.supportComplement D.dense_supportComplement hregular Y hunramified

end AlgebraicGeometry.FiniteEtale
