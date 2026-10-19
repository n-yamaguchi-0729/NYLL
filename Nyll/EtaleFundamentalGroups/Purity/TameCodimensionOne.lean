/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.TameDVREquiv
import Nyll.EtaleFundamentalGroups.Purity.CodimensionOneGenericFiber
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Ramification.TameDVR
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Opposites
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Closure

/-!
# Tameness at the actual codimension-one boundary stalks

The definition uses the canonical fraction-field map to a dense open and
all maximal quotient fields of the actual generic finite-etale algebra.
Existence of a DVR structure at each codimension-one boundary point is
included explicitly. This is the original setup of Stacks Project,
Section 58.31 (tag 0BSE), not an arbitrary family of replacement fields.

The comparison theorem transports tameness through a cover isomorphism.
It constructs the corresponding maximal ideals and quotient-field algebra
equivalences; invariance of integral closures, residue separability and
ramification indices is supplied by the existing compatible-equivalence
theorem. Thus changing the presentation of a genuine generic pullback does
not require an additional ramification-comparison assumption.
https://stacks.math.columbia.edu/tag/0BSE
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

attribute [local instance] Ideal.Quotient.field

namespace SchemeTheory

/-- An algebra equivalence transports tameness of every literal maximal
quotient through the actual corresponding quotient-field equivalence. -/
theorem tame_field_factors_of_algEquiv
    (R K A B : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra R A] [Algebra R B]
    [IsScalarTower R K A] [IsScalarTower R K B]
    (e : A ≃ₐ[K] B)
    (h : ∀ m : MaximalSpectrum A, IsTamelyRamifiedOverDVR R (A ⧸ m.asIdeal)) :
    ∀ m : MaximalSpectrum B, IsTamelyRamifiedOverDVR R (B ⧸ m.asIdeal) := by
  intro m
  let p : Ideal A := m.asIdeal.comap e.toRingHom
  have hp : p.IsMaximal := Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective
  let mA : MaximalSpectrum A := ⟨p, hp⟩
  let q : (A ⧸ p) ≃ₐ[K] (B ⧸ m.asIdeal) :=
    Ideal.quotientEquivAlg p m.asIdeal e
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective m.asIdeal).symm
  have hcoeff : q.toRingHom.comp (algebraMap R (A ⧸ p)) =
      (algebraMap R (B ⧸ m.asIdeal)).comp (RingEquiv.refl R).toRingHom := by
    apply RingHom.ext
    intro r
    change q (algebraMap R (A ⧸ p) r) = algebraMap R (B ⧸ m.asIdeal) r
    rw [IsScalarTower.algebraMap_apply R K (A ⧸ p), q.commutes,
      ← IsScalarTower.algebraMap_apply R K (B ⧸ m.asIdeal)]
  exact isTamelyRamifiedOverDVR_of_compatible_ringEquiv
    (RingEquiv.refl R) q.toRingEquiv hcoeff (h mA)

end SchemeTheory

namespace AlgebraicGeometry.FiniteEtale

/-- The field-factor tame condition is invariant under an isomorphism of
actual finite-etale covers over the same fraction-field spectrum. -/
theorem tame_field_factors_of_iso
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K]
    (Y Z : FiniteEtale (Spec (CommRingCat.of K))) (e : Y ≅ Z) :
    let A : CommAlgCat.FiniteEtale.{u} K :=
      (affineEquivalence (CommRingCat.of K)).functor.obj (Opposite.op Y)
    let B : CommAlgCat.FiniteEtale.{u} K :=
      (affineEquivalence (CommRingCat.of K)).functor.obj (Opposite.op Z)
    let : Algebra R A := Algebra.compHom A (algebraMap R K)
    let : Algebra R B := Algebra.compHom B (algebraMap R K)
    (∀ m : MaximalSpectrum A, SchemeTheory.IsTamelyRamifiedOverDVR R (A ⧸ m.asIdeal)) →
      ∀ m : MaximalSpectrum B, SchemeTheory.IsTamelyRamifiedOverDVR R (B ⧸ m.asIdeal) := by
  intro A B hRA hRB h
  have : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq' rfl
  let eCoordinates : B ≅ A :=
    (affineEquivalence (CommRingCat.of K)).functor.mapIso e.op
  let eAlgebra : A ≃ₐ[K] B :=
    (CommAlgCat.algEquivOfIso
      ((CommAlgCat.finiteEtale K).ι.mapIso eCoordinates)).symm
  exact SchemeTheory.tame_field_factors_of_algEquiv R K A B eAlgebra h

/-- Tame ramification over the ambient locally Noetherian scheme in
codimension one. The boundary stalks are DVRs, and every actual generic
field factor is tame over that very stalk, as in Stacks Section 58.31. -/
def IsTamelyRamifiedInCodimensionOne
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X)) (Y : FiniteEtale U.toScheme) : Prop :=
  ∀ (x : X) (hx : x ∉ U)
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)),
    ∃ hdomain : IsDomain (X.presheaf.stalk x),
      let : IsDomain (X.presheaf.stalk x) := hdomain
      ∃ hdvr : IsDiscreteValuationRing (X.presheaf.stalk x),
        let : IsDiscreteValuationRing (X.presheaf.stalk x) := hdvr
        let K := FractionRing (X.presheaf.stalk x)
        let r : Spec (CommRingCat.of K) ⟶ U.toScheme :=
          Scheme.denseOpenDVRFractionFieldMap U hU x hx hdim
        let A : CommAlgCat.FiniteEtale.{u} K :=
          (affineEquivalence (CommRingCat.of K)).functor.obj
            (Opposite.op ((pullback r).obj Y))
        let : Algebra (X.presheaf.stalk x) A :=
          Algebra.compHom A (algebraMap (X.presheaf.stalk x) K)
        ∀ m : MaximalSpectrum A,
          SchemeTheory.IsTamelyRamifiedOverDVR (X.presheaf.stalk x) (A ⧸ m.asIdeal)

end AlgebraicGeometry.FiniteEtale
