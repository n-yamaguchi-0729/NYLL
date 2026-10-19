/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryStalkTame
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.StandardCover
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.TameDVREquiv
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.SchemeTheory.Affine.StalkFractionField
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Ramification.TameDVR
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Actual field factors of a standard root cover at a boundary stalk

A scheme comparison with `Spec L`, including its projection to `Spec K`,
induces a `K`-algebra equivalence from the actual affine finite-etale
coordinate algebra to `L`. Each maximal quotient field is then identified
with `L` by composing the inverse equivalence with the quotient map.

For the standard root cover every input comparison is supplied by the
existing boundary-stalk theorem. Thus finite separability, degree and
tameness are statements about all literal maximal quotients of the actual
generic pullback, not about an arbitrarily chosen replacement field.

This supplies the field-factor condition used in the codimension-one tame
predicate of Stacks Project, Section 58.31 (tag `0BSE`), for the boundary
stalks of Example 58.31.4 (tag `0EYF`).
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] Ideal.Quotient.field

namespace EtaleFundamentalGroups.Kummer

/-- The existing affine finite-etale equivalence uses global sections with
the scalar map obtained from the original scheme morphism. Consequently a
comparison over the original spectrum determines an algebra equivalence. -/
private def genericCoordinatesAlgEquivField
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (Y : FiniteEtale (Spec (CommRingCat.of K)))
    (e : Spec (CommRingCat.of L) ≅ Y.left)
    (he : e.hom ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ((FiniteEtale.affineEquivalence (CommRingCat.of K)).functor.obj
      (Opposite.op Y)) ≃ₐ[K] L := by
  let eSections : Γ(Y.left, ⊤) ≃+* L :=
    ((Scheme.Γ.mapIso e.op) ≪≫ Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
  have hscalar :
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.hom.appTop) ≫
          e.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom =
        CommRingCat.ofHom (algebraMap K L) := by
    calc
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.hom.appTop) ≫
          e.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (e.hom ≫ Y.hom).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      _ = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap K L))).appTop ≫
            (Scheme.ΓSpecIso (CommRingCat.of L)).hom :=
        congrArg (fun φ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) =>
          (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ φ.appTop ≫
            (Scheme.ΓSpecIso (CommRingCat.of L)).hom) he
      _ = CommRingCat.ofHom (algebraMap K L) := by
        rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  refine AlgEquiv.ofRingEquiv (f := eSections) ?_
  intro k
  change ((e.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom)
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.hom.appTop).hom k) =
    algebraMap K L k
  exact ConcreteCategory.congr_hom hscalar k

/-- Each actual maximal quotient of an algebra identified with a field is
that same field, by the literal quotient map and the inverse identification. -/
private def maximalQuotientAlgEquivOfField
    (K L A : Type u) [CommRing K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] (e : A ≃ₐ[K] L) (m : MaximalSpectrum A) :
    L ≃ₐ[K] (A ⧸ m.asIdeal) := by
  let q : L →ₐ[K] (A ⧸ m.asIdeal) :=
    (Ideal.Quotient.mkₐ K m.asIdeal).comp e.symm.toAlgHom
  refine AlgEquiv.ofBijective q ⟨RingHom.injective q.toRingHom, ?_⟩
  exact Ideal.Quotient.mk_surjective.comp e.symm.surjective

/-- Tameness of the field computed by an actual generic-fibre comparison
holds for all maximal quotient fields of the coordinate algebra chosen by
the existing affine finite-etale equivalence. -/
private theorem genericCoordinates_allFieldFactors_tame
    (R K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Field L] [Algebra R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    (Y : FiniteEtale (Spec (CommRingCat.of K)))
    (e : Spec (CommRingCat.of L) ≅ Y.left)
    (he : e.hom ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    {n : ℕ} (hdegree : Module.finrank K L = n)
    (htame : SchemeTheory.IsTamelyRamifiedOverDVR R L) :
    let A : CommAlgCat.FiniteEtale.{u} K :=
      (FiniteEtale.affineEquivalence (CommRingCat.of K)).functor.obj (Opposite.op Y)
    let : Algebra R A := Algebra.compHom A (algebraMap R K)
    ∀ m : MaximalSpectrum A,
      Module.Finite K (A ⧸ m.asIdeal) ∧
        Algebra.IsSeparable K (A ⧸ m.asIdeal) ∧
        Module.finrank K (A ⧸ m.asIdeal) = n ∧
        SchemeTheory.IsTamelyRamifiedOverDVR R (A ⧸ m.asIdeal) := by
  intro A hRA m
  have : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq' rfl
  let eA : A ≃ₐ[K] L := genericCoordinatesAlgEquivField K L Y e he
  let em : L ≃ₐ[K] (A ⧸ m.asIdeal) := maximalQuotientAlgEquivOfField K L A eA m
  have hcoefficient : em.toRingHom.comp (algebraMap R L) =
      (algebraMap R (A ⧸ m.asIdeal)).comp (RingEquiv.refl R).toRingHom := by
    apply RingHom.ext
    intro r
    change em (algebraMap R L r) = algebraMap R (A ⧸ m.asIdeal) r
    rw [IsScalarTower.algebraMap_apply R K L, em.commutes,
      ← IsScalarTower.algebraMap_apply R K (A ⧸ m.asIdeal)]
  refine ⟨Module.Finite.equiv em.toLinearEquiv,
    (AlgEquiv.Algebra.isSeparable_iff em).mp inferInstance,
    em.toLinearEquiv.finrank_eq.symm.trans hdegree, ?_⟩
  exact SchemeTheory.isTamelyRamifiedOverDVR_of_compatible_ringEquiv
    (RingEquiv.refl R) em.toRingEquiv hcoefficient htame

/-- The literal finite-etale cover over the distinguished open, bundled
once together with the finite and etale proofs supplied by its root equation. -/
def standardKummerAwayCover
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (hnUnit : IsUnit (n : A)) (f : A) :
    FiniteEtale (Spec (CommRingCat.of (Localization.Away f))) := by
  let B := AdjoinRoot (Polynomial.X ^ n - Polynomial.C f)
  let π := Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A B) f))
  have hproperties := finite_etale_awayMap_adjoinRoot hn hnUnit f
  have : IsFinite π :=
    (IsFinite.SpecMap_iff
      (CommRingCat.ofHom (Localization.awayMap (algebraMap A B) f))).mpr hproperties.1
  have : Etale π :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hproperties.2
  have : IsFiniteEtale π := IsFiniteEtale.mk
  exact FiniteEtale.mk π

open Polynomial

/-- Every literal maximal quotient field of the actual generic pullback at
a boundary stalk is finite separable of degree `n` and tame over that stalk.
The field-factor comparison is derived from the original root equation. -/
theorem standardKummerCover_boundaryStalk_allFieldFactors_tame
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : A)) :
    let x : PrimeSpectrum A := ⟨P, inferInstance⟩
    let R : CommRingCat.{u} := (Spec (CommRingCat.of A)).presheaf.stalk x
    let V := Localization.AtPrime P
    let XAway : FiniteEtale (Spec (CommRingCat.of (Localization.Away f))) :=
      standardKummerAwayCover hn hnUnit f
    let : IsRegularLocalRing V :=
      SchemeTheory.isRegularLocalRing_localizationAtPrime_of_reduced_quotient f hf P hP
    let : IsDomain V := IsRegularLocalRing.isDomain V
    let : IsDiscreteValuationRing V :=
      SchemeTheory.isDiscreteValuationRing_localizationAtPrime_of_reduced_quotient f hf P hP
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
  intro x R V XAway hregular hdomainV hdvrV eStalk hdomainR hdvrR
  let B := AdjoinRoot (X ^ n - C (algebraMap A V f))
  obtain ⟨hdomainB, hdata⟩ := standardKummerCover_tameBoundaryStalkGenericFiber f hf P hP hn hnUnit
  have : IsDomain B := hdomainB
  let : Module.FaithfullyFlat V B := faithfullyFlat_adjoinRoot_X_pow_sub_C hn (algebraMap A V f)
  let L := FractionRing B
  let : Algebra (FractionRing V) L := FractionRing.liftAlgebra V L
  let c : FractionRing R ≃+* FractionRing V := Spec.stalkFractionRingEquiv (CommRingCat.of A) x
  let : Algebra (FractionRing R) L :=
    ((algebraMap (FractionRing V) L).comp c.toRingHom).toAlgebra
  let : Algebra R L := Algebra.compHom L (algebraMap R (FractionRing R))
  have : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hfinite, hseparable, hdegree, htame, r, hr, e, he⟩ := hdata
  have : Module.Finite (FractionRing R) L := hfinite
  have : Algebra.IsSeparable (FractionRing R) L := hseparable
  refine ⟨r, hr, ?_⟩
  intro Y G hRG
  exact genericCoordinates_allFieldFactors_tame R (FractionRing R) L Y e he hdegree htame

end EtaleFundamentalGroups.Kummer
