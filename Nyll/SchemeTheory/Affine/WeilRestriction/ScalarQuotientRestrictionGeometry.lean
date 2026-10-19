/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestrictionScheme
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionFibers
import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitCover

/-! # Geometry of actual scalar quotient restriction -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

open UnitNormPolynomial ProjectiveUnitCharts

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {n m : ℕ} (bA : Basis (Fin (n + 1)) R A) (bB : Basis (Fin (m + 1)) R B)
  (f : A →ₐ[R] B)

/-- The actual normalized projective-chart sections transfer a property from unit
restriction to scalar quotient restriction whenever it is local on the target and
stable under base change. The Cartesian square was constructed from actual scalar orbits. -/
private theorem property_quotientRestrictionMap (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
    (hP : P (restrictionMap bA bB f)) : P (quotientRestrictionMap bA bB f) := by
  let 𝒰 := Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of (ProjectiveUnitOpen.CoordinateRing bB))
    (chartElement bB) (span_chartElement bB)
  apply IsZariskiLocalAtTarget.of_openCover 𝒰.openCover
  intro j
  change Fin (m + 1) at j
  let s : Spec (CommRingCat.of (LocalChart bB j)) ⟶ ProjectiveUnitOpen.carrier bB :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (ProjectiveUnitOpen.CoordinateRing bB) (LocalChart bB j)))
  change P (pullback.snd (quotientRestrictionMap bA bB f) s)
  have hs : IsPullback
      (pullback.fst (quotientRestrictionMap bA bB f) s)
      (pullback.snd (quotientRestrictionMap bA bB f) s)
      (quotientRestrictionMap bA bB f)
      (localSectionMap bB j ≫ ProjectiveUnitOpen.quotientMap bB) := by
    rw [localSectionMap_quotientMap bB j]
    exact IsPullback.of_hasPullback _ _
  exact P.of_isPullback
    (hs.of_right' (quotientRestrictionMap_isPullback bA bB f)) hP

/-- Actual scalar quotient restriction is surjective for finite free algebra surjections,
over arbitrary coefficient rings. -/
theorem surjective_quotientRestrictionMap (hf : Function.Surjective f) :
    Surjective (quotientRestrictionMap bA bB f) := by
  have : Surjective (restrictionMap bA bB f) := surjective_restrictionMap bA bB f hf
  have : Surjective (ProjectiveUnitOpen.quotientMap bB) := surjective_quotientMap bB
  have hcomp : Surjective (restrictionMap bA bB f ≫ ProjectiveUnitOpen.quotientMap bB) :=
    inferInstance
  have : Surjective (ProjectiveUnitOpen.quotientMap bA ≫ quotientRestrictionMap bA bB f) := by
    rw [(quotientRestrictionMap_isPullback bA bB f).w]
    exact hcomp
  exact Surjective.of_comp (ProjectiveUnitOpen.quotientMap bA)
    (quotientRestrictionMap bA bB f)

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

open UnitNormPolynomial ProjectiveUnitCharts

variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  {n m : ℕ} (bA : Basis (Fin (n + 1)) K A) (bB : Basis (Fin (m + 1)) K B)
  (f : A →ₐ[K] B) (hf : Function.Surjective f)

include hf in
/-- The actual scalar quotient restriction induced by a finite-dimensional algebra
surjection is smooth. The local splittings are the concrete normalized chart units. -/
theorem smooth_quotientRestrictionMap : Smooth (quotientRestrictionMap bA bB f) := by
  have : Module.Finite K A := Module.Finite.of_basis bA
  have : HasAffineProperty (@Smooth : MorphismProperty Scheme.{u})
      (sourceAffineLocally RingHom.Smooth) :=
    HasRingHomProperty.HasAffineProperty (P := (@Smooth : MorphismProperty Scheme.{u}))
  let 𝒰 := Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of (ProjectiveUnitOpen.CoordinateRing bB))
    (chartElement bB) (span_chartElement bB)
  have : ∀ i, IsAffine (𝒰.openCover.X i) := by
    intro i
    change Fin (m + 1) at i
    change IsAffine (Spec (CommRingCat.of (LocalChart bB i)))
    infer_instance
  apply HasAffineProperty.of_openCover (P := (@Smooth : MorphismProperty Scheme.{u})) 𝒰.openCover
  intro j
  change Fin (m + 1) at j
  let s : Spec (CommRingCat.of (LocalChart bB j)) ⟶ ProjectiveUnitOpen.carrier bB :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (ProjectiveUnitOpen.CoordinateRing bB) (LocalChart bB j)))
  change sourceAffineLocally RingHom.Smooth (pullback.snd (quotientRestrictionMap bA bB f) s)
  apply (HasAffineProperty.iff_of_isAffine (P := (@Smooth : MorphismProperty Scheme.{u}))).mp
  have hs : IsPullback
      (pullback.fst (quotientRestrictionMap bA bB f) s)
      (pullback.snd (quotientRestrictionMap bA bB f) s)
      (quotientRestrictionMap bA bB f)
      (localSectionMap bB j ≫ ProjectiveUnitOpen.quotientMap bB) := by
    rw [localSectionMap_quotientMap bB j]
    exact IsPullback.of_hasPullback _ _
  exact smooth_isStableUnderBaseChange.of_isPullback
    (hs.of_right' (quotientRestrictionMap_isPullback bA bB f))
    (smooth_restrictionMap bB f hf bA)

include hf in
/-- Every geometric fibre of the actual scalar quotient restriction is irreducible. -/
theorem geometricallyIrreducible_quotientRestrictionMap :
    GeometricallyIrreducible (quotientRestrictionMap bA bB f) := by
  have : Module.Finite K A := Module.Finite.of_basis bA
  constructor
  exact property_quotientRestrictionMap bA bB f (geometrically (IrreducibleSpace ·))
    (geometricallyIrreducible_restrictionMap bA bB f hf).geometrically_irreducibleSpace

include hf in
/-- In particular every geometric fibre of scalar quotient restriction is connected. -/
theorem geometricallyConnected_quotientRestrictionMap :
    GeometricallyConnected (quotientRestrictionMap bA bB f) := by
  constructor
  intro L _ y Z fst snd h
  have : IrreducibleSpace Z :=
    (geometricallyIrreducible_quotientRestrictionMap bA bB f hf).geometrically_irreducibleSpace
      y fst snd h
  infer_instance

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
