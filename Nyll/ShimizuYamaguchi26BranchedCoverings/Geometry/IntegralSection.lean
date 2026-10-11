/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ZeroSection
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Set.Image
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Homeomorph.Defs

/-!
# Integral sections with primitive homogeneous coordinates

Bézout coefficients for an integer pair construct an actual section of the
projective line over `Spec ℤ`. The zero section of the affine chart is first
sent to infinity by exchanging coordinates, and then transported by the
inverse Bézout coordinate change. The resulting section is a closed immersion,
and its image is exactly the projective zero locus of `v*T₀-u*T₁`.

This supplies the integral section underlying the first assertion of
Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem range_zeroSection_comp_swap :
    Set.range (zeroSection ℤ ≫ (projectiveCoordinateSwap ℤ).hom) =
      (infinityComplement ℤ : Set (ProjectiveLine ℤ))ᶜ := by
  have hzero : Set.range (zeroSection ℤ) =
      (projectiveCoordinateSwap ℤ).hom ⁻¹'
        (infinityComplement ℤ : Set (ProjectiveLine ℤ))ᶜ := by
    rw [Set.preimage_compl]
    change Set.range (zeroSection ℤ) =
      (((projectiveCoordinateSwap ℤ).hom ⁻¹ᵁ infinityComplement ℤ :
        (ProjectiveLine ℤ).Opens) : Set (ProjectiveLine ℤ))ᶜ
    rw [projectiveCoordinateSwap, integralCoordinateChange_preimage_infinity]
    change Set.range (zeroSection ℤ) =
      (ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (0 : ℤ) 1) : Set (ProjectiveLine ℤ))ᶜ
    rw [ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl, range_zeroSection]
  change Set.range (fun x => (projectiveCoordinateSwap ℤ).hom (zeroSection ℤ x)) = _
  rw [Set.range_comp', hzero]
  exact Set.image_preimage_eq _ (Scheme.homeoOfIso (projectiveCoordinateSwap ℤ)).surjective

/-- The actual integral section associated to coordinates and Bézout coefficients. -/
def integralSection (u v a b : ℤ) (hab : a * u + b * v = 1) :
    Spec (CommRingCat.of ℤ) ⟶ ProjectiveLine ℤ :=
  (zeroSection ℤ ≫ (projectiveCoordinateSwap ℤ).hom) ≫
    (integralCoordinateChange u v a b hab).inv

/-- The constructed morphism is a section of the integral projective line. -/
theorem integralSection_comp_π (u v a b : ℤ) (hab : a * u + b * v = 1) :
    integralSection u v a b hab ≫ ProjSpace.π ℤ 1 =
      𝟙 (Spec (CommRingCat.of ℤ)) :=
  specZIsTerminal.hom_ext _ _

/-- Every integral section constructed from a primitive coordinate pair is closed. -/
instance (u v a b : ℤ) (hab : a * u + b * v = 1) :
    IsClosedImmersion (integralSection u v a b hab) := by
  have : IsClosedImmersion (integralSection u v a b hab ≫ ProjSpace.π ℤ 1) := by
    rw [integralSection_comp_π]
    infer_instance
  exact IsClosedImmersion.of_comp (integralSection u v a b hab) (ProjSpace.π ℤ 1)

/-- The image of the actual integral section is its homogeneous linear zero locus. -/
theorem range_integralSection (u v a b : ℤ) (hab : a * u + b * v = 1) :
    Set.range (integralSection u v a b hab) =
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation u v} := by
  let e : ProjectiveLine ℤ ≅ ProjectiveLine ℤ :=
    integralCoordinateChange u v a b hab
  change Set.range (fun x => e.inv ((zeroSection ℤ ≫ (projectiveCoordinateSwap ℤ).hom) x)) = _
  rw [Set.range_comp', range_zeroSection_comp_swap]
  calc
    e.inv '' (infinityComplement ℤ : Set (ProjectiveLine ℤ))ᶜ =
        e.hom ⁻¹' (infinityComplement ℤ : Set (ProjectiveLine ℤ))ᶜ := by
      exact congrFun (Scheme.homeoOfIso e).image_symm _
    _ = ((e.hom ⁻¹ᵁ infinityComplement ℤ :
        (ProjectiveLine ℤ).Opens) : Set (ProjectiveLine ℤ))ᶜ :=
      Set.preimage_compl
    _ = (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation u v) : Set (ProjectiveLine ℤ))ᶜ := by
      rw [e, integralCoordinateChange_preimage_infinity]
    _ = ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation u v} := by
      change (ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation u v) : Set (ProjectiveLine ℤ))ᶜ = _
      rw [ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]

end ShimizuYamaguchi26BranchedCoverings
