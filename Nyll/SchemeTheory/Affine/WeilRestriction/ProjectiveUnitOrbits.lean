/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitCover
import Mathlib.Algebra.Group.Commute.Units

/-!
# Scalar orbits on the normalized projective unit charts

An actual unit over a point of a standard chart is a unique scalar
multiple of the constructed normalized unit. The scalar is its
distinguished coordinate, whose invertibility follows from the norm.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module HomogeneousLocalization
open scoped TensorProduct

universe u

namespace SchemeTheory.Affine.ProjectiveUnitCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "N" => UnitNormPolynomial.normPolynomial b

private theorem mixed_mem (j i : Fin (n + 1)) :
    MvPolynomial.X i * MvPolynomial.X j ^ n ∈ 𝒜 (1 • (n + 1)) := by
  apply (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
  simpa only [one_smul, one_mul, Nat.add_comm] using
    (MvPolynomial.isHomogeneous_X R i).mul ((MvPolynomial.isHomogeneous_X R j).pow n)

/-- The mixed degree-zero coordinate used to compare affine and normalized coordinates. -/
def mixedCoordinate (j i : Fin (n + 1)) : ProjectiveUnitOpen.CoordinateRing b :=
  Away.mk 𝒜 (ProjectiveUnitOpen.norm_mem b) 1
    (MvPolynomial.X i * MvPolynomial.X j ^ n) (mixed_mem j i)

/-- The standard coordinate ratio times the chart denominator is the mixed
coordinate on the actual overlap. -/
theorem overlap_ratio (j i : Fin (n + 1)) :
    fromStandard b j (ProjSpace.ratio R n j i) * fromNorm b j (chartElement b j) =
      fromNorm b j (mixedCoordinate b j i) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, fromStandard, fromNorm,
    ProjSpace.ratio, chartElement, Away.isLocalizationElem, mixedCoordinate,
    awayMap_mk, Away.val_mk, Localization.mk_mul, pow_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Normalization divides the mixed coordinates by the chart coordinate. -/
theorem normalizedCoordinates_mul_chartElement
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) (i : Fin (n + 1)) :
    normalizedCoordinates b f j hj i * f (chartElement b j) = f (mixedCoordinate b j i) := by
  have h := congrArg (intersectionPoint b f j hj) (overlap_ratio b j i)
  rw [map_mul, intersectionPoint_fromNorm, intersectionPoint_fromNorm] at h
  exact h

/-- The chart coordinate evaluated at a unit is its distinguished
coordinate to the rank divided by its norm. -/
theorem norm_mul_projectivePoint_chartElement (a : (S ⊗[R] A)ˣ) (j : Fin (n + 1)) :
    MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) N *
        ProjectiveUnitOpen.projectivePoint b a (chartElement b j) =
      UnitNormPolynomial.coordinates b (a : S ⊗[R] A) j ^ (n + 1) := by
  have h := projectivePoint_mk b a 1 (MvPolynomial.X j ^ (n + 1))
    (by simpa only [one_smul, smul_eq_mul, mul_one, one_mul] using
      SetLike.pow_mem_graded (n + 1) (ProjSpace.X_mem_one R n j))
  simpa only [chartElement, Away.isLocalizationElem, pow_one, map_pow,
    MvPolynomial.aeval_X] using h

/-- Mixed projective coordinates recover the products of the actual
affine coordinates after multiplying by the norm. -/
theorem norm_mul_projectivePoint_mixedCoordinate (a : (S ⊗[R] A)ˣ)
    (j i : Fin (n + 1)) :
    MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) N *
        ProjectiveUnitOpen.projectivePoint b a (mixedCoordinate b j i) =
      UnitNormPolynomial.coordinates b (a : S ⊗[R] A) i *
        UnitNormPolynomial.coordinates b (a : S ⊗[R] A) j ^ n := by
  simpa only [mixedCoordinate, pow_one, map_mul, map_pow, MvPolynomial.aeval_X] using
    projectivePoint_mk b a 1 (MvPolynomial.X i * MvPolynomial.X j ^ n) (mixed_mem j i)

/-- The distinguished coordinate of any unit over the chart is invertible. -/
theorem isUnit_coordinate_of_projectivePoint_eq
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j)))
    (a : (S ⊗[R] A)ˣ) (ha : ProjectiveUnitOpen.projectivePoint b a = f.toRingHom) :
    IsUnit (UnitNormPolynomial.coordinates b (a : S ⊗[R] A) j) := by
  apply isUnit_pow_succ_iff.mp
  rw [← norm_mul_projectivePoint_chartElement b a j, ha]
  apply IsUnit.mul _ hj
  apply (UnitNormPolynomial.isUnit_aeval_normPolynomial_iff b _).mpr
  rw [UnitNormPolynomial.element_coordinates]
  exact a.isUnit

/-- Every affine unit over the chart is a scalar multiple of the normalized
unit, with scalar its distinguished coordinate. -/
theorem coordinates_eq_scalar_normalized
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j)))
    (a : (S ⊗[R] A)ˣ) (ha : ProjectiveUnitOpen.projectivePoint b a = f.toRingHom)
    (i : Fin (n + 1)) :
    UnitNormPolynomial.coordinates b (a : S ⊗[R] A) j *
        normalizedCoordinates b f j hj i =
      UnitNormPolynomial.coordinates b (a : S ⊗[R] A) i := by
  apply ((isUnit_coordinate_of_projectivePoint_eq b f j hj a ha).pow n).mul_left_cancel
  have hc := norm_mul_projectivePoint_chartElement b a j
  have hm := norm_mul_projectivePoint_mixedCoordinate b a j i
  rw [ha] at hc hm
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hc hm
  calc
    _ = normalizedCoordinates b f j hj i *
        UnitNormPolynomial.coordinates b (a : S ⊗[R] A) j ^ (n + 1) := by
      rw [pow_succ]
      ring
    _ = normalizedCoordinates b f j hj i *
        (MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) N *
          f (chartElement b j)) := by rw [hc]
    _ = MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) N *
        (normalizedCoordinates b f j hj i * f (chartElement b j)) := by ring
    _ = _ := by rw [normalizedCoordinates_mul_chartElement, hm, mul_comm]

/-- On every standard chart the fiber of the projective-class map consists
of unique scalar multiples of its explicitly constructed normalized unit. -/
theorem existsUnique_scalar_normalizedUnit
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j)))
    (a : (S ⊗[R] A)ˣ) (ha : ProjectiveUnitOpen.projectivePoint b a = f.toRingHom) :
    ∃! r : Sˣ, a = ProjectiveUnitOpen.scalarMul r (normalizedUnit b f j hj) := by
  let h : IsUnit (UnitNormPolynomial.coordinates b (a : S ⊗[R] A) j) :=
    isUnit_coordinate_of_projectivePoint_eq b f j hj a ha
  refine ⟨h.unit, ?_, ?_⟩
  · apply Units.ext
    apply (Algebra.TensorProduct.basis S b).repr.injective
    apply Finsupp.ext
    intro i
    change UnitNormPolynomial.coordinates b (a : S ⊗[R] A) i =
      UnitNormPolynomial.coordinates b
        (ProjectiveUnitOpen.scalarMul h.unit (normalizedUnit b f j hj) : S ⊗[R] A) i
    rw [ProjectiveUnitOpen.coordinates_scalarMul, coordinates_normalizedUnit, h.unit_spec]
    exact (coordinates_eq_scalar_normalized b f j hj a ha i).symm
  · intro r hr
    apply Units.ext
    have hc := congrArg (fun z : (S ⊗[R] A)ˣ =>
      UnitNormPolynomial.coordinates b (z : S ⊗[R] A) j) hr
    simp only [ProjectiveUnitOpen.coordinates_scalarMul, coordinates_normalizedUnit,
      normalizedCoordinates_self, mul_one] at hc
    exact hc.symm.trans h.unit_spec.symm

/-- On a normalized chart, the fiber of the actual projective-class map
is explicitly equivalent to the scalar units. -/
def normalizedFiberEquivUnits
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) :
    {a : (S ⊗[R] A)ˣ // ProjectiveUnitOpen.projectivePoint b a = f.toRingHom} ≃ Sˣ where
  toFun a := (isUnit_coordinate_of_projectivePoint_eq b f j hj a.1 a.2).unit
  invFun r := ⟨ProjectiveUnitOpen.scalarMul r (normalizedUnit b f j hj), by
    rw [ProjectiveUnitOpen.projectivePoint_scalarMul, projectivePoint_normalizedUnit]⟩
  left_inv a := by
    apply Subtype.ext
    obtain ⟨r, hr, _⟩ := existsUnique_scalar_normalizedUnit b f j hj a.1 a.2
    have hc := congrArg (fun z : (S ⊗[R] A)ˣ =>
      UnitNormPolynomial.coordinates b (z : S ⊗[R] A) j) hr
    simp only [ProjectiveUnitOpen.coordinates_scalarMul, coordinates_normalizedUnit,
      normalizedCoordinates_self, mul_one] at hc
    have he : (isUnit_coordinate_of_projectivePoint_eq b f j hj a.1 a.2).unit = r := by
      apply Units.ext
      exact (IsUnit.unit_spec _).trans hc
    change ProjectiveUnitOpen.scalarMul
      (isUnit_coordinate_of_projectivePoint_eq b f j hj a.1 a.2).unit
      (normalizedUnit b f j hj) = a.1
    rw [he]
    exact hr.symm
  right_inv r := by
    apply Units.ext
    simp only [IsUnit.unit_spec, ProjectiveUnitOpen.coordinates_scalarMul,
      coordinates_normalizedUnit, normalizedCoordinates_self, mul_one]

end SchemeTheory.Affine.ProjectiveUnitCharts
