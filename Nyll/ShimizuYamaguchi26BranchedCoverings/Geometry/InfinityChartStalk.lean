/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.LocalizedInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The actual projective stalk at the infinity chart point

Swapping the homogeneous coordinates turns the standard affine chart into
the chart `T₀ ≠ 0`. At the prime `(maximalIdeal R, X)`, the open immersion
identifies the stalk of the projective line with the prime localization of
`R[X]`. Polynomial germs are constructed from the actual structure-sheaf
germ on `Spec R[X]` and the inverse chart stalk map. The stalk isomorphism
sends these germs to the usual localization map.

This identifies the ring in the infinity-chart intersection calculation
with an actual projective local ring, as needed for Lemma 2.3 of Ryoji
Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private def infinityCoordinateSwap (R : Type u) [CommRing R] :
    ProjectiveLine R ≅ ProjectiveLine R :=
  integralCoordinateChange (0 : R) 1 0 1
    (by rw [zero_mul, one_mul, zero_add])

/-- The affine chart at infinity, with coordinate `T₁ / T₀`. -/
def infinityChartEmbedding (R : Type u) [CommRing R] :
    Spec (CommRingCat.of R[X]) ⟶ ProjectiveLine R :=
  standardChartEmbedding R ≫ (infinityCoordinateSwap R).hom

instance (R : Type u) [CommRing R] : IsOpenImmersion (infinityChartEmbedding R) := by
  unfold infinityChartEmbedding
  infer_instance

/-- The infinity chart is the actual open `T₀ ≠ 0` in the projective line. -/
theorem infinityChartEmbedding_opensRange (R : Type u) [CommRing R] :
    (infinityChartEmbedding R).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (MvPolynomial.X (0 : Fin 2)) := by
  have hswap : (infinityCoordinateSwap R).hom = (infinityCoordinateSwap R).inv := rfl
  rw [infinityChartEmbedding, Scheme.Hom.opensRange_comp,
    standardChartEmbedding_opensRange, hswap, Scheme.Hom.inv_image]
  rw [infinityCoordinateSwap, integralCoordinateChange_preimage_infinity]
  simp only [linearSectionEquation, map_one, map_zero, one_mul, zero_mul, sub_zero]

/-- The prime of the infinity chart above the closed point of the local base. -/
def infinityChartClosedPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    PrimeSpectrum R[X] :=
  ⟨infinityChartClosedPointIdeal R, inferInstance⟩

/-- The corresponding actual point of the projective line. -/
def projectiveInfinityPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    ProjectiveLine R :=
  infinityChartEmbedding R (infinityChartClosedPoint R)

/-- The projective stalk is the localization at the concrete infinity chart prime. -/
def projectiveInfinityStalkEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    (ProjectiveLine R).presheaf.stalk (projectiveInfinityPoint R) ≃+*
      InfinityChartLocalRing R :=
  ((asIso ((infinityChartEmbedding R).stalkMap (infinityChartClosedPoint R))) ≪≫
    Spec.stalkIso (CommRingCat.of R[X]) (infinityChartClosedPoint R)).commRingCatIsoToRingEquiv

/-- A polynomial defines a projective local germ through the actual affine
structure-sheaf germ and the inverse stalk map of the chart. -/
def infinityChartGerm (R : Type u) [CommRing R] [IsLocalRing R] :
    R[X] →+* (ProjectiveLine R).presheaf.stalk (projectiveInfinityPoint R) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv ≫
    (Spec (CommRingCat.of R[X])).presheaf.germ ⊤ (infinityChartClosedPoint R) trivial ≫
    (asIso ((infinityChartEmbedding R).stalkMap (infinityChartClosedPoint R))).inv).hom

/-- The actual chart germ becomes the standard polynomial localization map. -/
theorem projectiveInfinityStalkEquiv_germ (R : Type u) [CommRing R] [IsLocalRing R]
    (f : R[X]) :
    projectiveInfinityStalkEquiv R (infinityChartGerm R f) =
      algebraMap R[X] (InfinityChartLocalRing R) f := by
  change (Spec.stalkIso (CommRingCat.of R[X]) (infinityChartClosedPoint R)).hom
    ((asIso ((infinityChartEmbedding R).stalkMap (infinityChartClosedPoint R))).hom
      ((asIso ((infinityChartEmbedding R).stalkMap (infinityChartClosedPoint R))).inv
        ((Spec (CommRingCat.of R[X])).presheaf.germ ⊤ (infinityChartClosedPoint R) trivial
          ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv f)))) = _
  rw [CommRingCat.hom_inv_apply]
  have h := ConcreteCategory.congr_hom
    (Spec.germ_stalkMapIso_hom (R := CommRingCat.of R[X]) (x := infinityChartClosedPoint R))
    ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv f)
  simpa only [CommRingCat.comp_apply, CommRingCat.hom_inv_apply] using h

end ShimizuYamaguchi26BranchedCoverings
