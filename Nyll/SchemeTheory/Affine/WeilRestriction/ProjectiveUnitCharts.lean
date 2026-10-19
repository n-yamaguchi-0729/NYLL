/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitOpen
import Mathlib.Tactic.Ring.RingNF

/-!
# Normalized local lifts of the projective norm open

The overlap of the norm chart and a standard projective coordinate chart
is a localization in either direction. Evaluating the standard ratios
there supplies normalized coordinates whose norm is a unit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module HomogeneousLocalization
open AlgebraicCurves.Geometry.Sheaves.Proofs.ProjectivePresentation.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

namespace SchemeTheory.Affine.ProjectiveUnitCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "P" => MvPolynomial (Fin (n + 1)) R
local notation "N" => UnitNormPolynomial.normPolynomial b

/-- The ordinary projective chart with the chosen coordinate normalized to one. -/
abbrev StandardChart (j : Fin (n + 1)) := Away 𝒜 (MvPolynomial.X j)

/-- The actual overlap of the norm chart and a standard projective chart. -/
abbrev Intersection (j : Fin (n + 1)) := Away 𝒜 (N * MvPolynomial.X j)

/-- The degree-zero function cutting out the standard coordinate chart
inside the norm open. -/
def chartElement (j : Fin (n + 1)) : ProjectiveUnitOpen.CoordinateRing b :=
  Away.isLocalizationElem (ProjectiveUnitOpen.norm_mem b) (ProjSpace.X_mem_one R n j)

/-- Restriction from the norm open to its intersection with a coordinate chart. -/
def fromNorm (j : Fin (n + 1)) :
    ProjectiveUnitOpen.CoordinateRing b →+* Intersection b j :=
  awayMap 𝒜 (ProjSpace.X_mem_one R n j) rfl

/-- Restriction from a coordinate chart to its intersection with the norm open. -/
def fromStandard (j : Fin (n + 1)) : StandardChart (R := R) j →+* Intersection b j :=
  awayMap 𝒜 (ProjectiveUnitOpen.norm_mem b) (mul_comm N (MvPolynomial.X j))

instance intersectionAlgebra (j : Fin (n + 1)) :
    Algebra (ProjectiveUnitOpen.CoordinateRing b) (Intersection b j) :=
  (fromNorm b j).toAlgebra

/-- The overlap is the principal localization at the displayed chart function. -/
instance intersectionLocalization (j : Fin (n + 1)) :
    IsLocalization.Away (chartElement b j) (Intersection b j) :=
  Away.isLocalization_mul (ProjectiveUnitOpen.norm_mem b)
    (ProjSpace.X_mem_one R n j) rfl (Nat.succ_ne_zero n)

/-- The homogeneous norm divided by the distinguished coordinate to its degree. -/
def standardNorm (j : Fin (n + 1)) : StandardChart (R := R) j :=
  Away.isLocalizationElem (ProjSpace.X_mem_one R n j) (ProjectiveUnitOpen.norm_mem b)

/-- On the overlap, the normalized norm is invertible. -/
theorem isUnit_fromStandard_standardNorm (j : Fin (n + 1)) :
    IsUnit (fromStandard b j (standardNorm b j)) := by
  let : Algebra (StandardChart (R := R) j) (Intersection b j) :=
    (fromStandard b j).toAlgebra
  have : IsLocalization.Away (standardNorm b j) (Intersection b j) :=
    Away.isLocalization_mul (ProjSpace.X_mem_one R n j)
      (ProjectiveUnitOpen.norm_mem b) (mul_comm N (MvPolynomial.X j)) one_ne_zero
  exact IsLocalization.Away.algebraMap_isUnit (S := Intersection b j) (standardNorm b j)

/-- The two restriction maps agree on coefficients. -/
theorem fromStandard_algebraMap (j : Fin (n + 1)) (r : R) :
    fromStandard b j (algebraMap R (StandardChart (R := R) j) r) =
      fromNorm b j (algebraMap R (ProjectiveUnitOpen.CoordinateRing b) r) := by
  change awayMap 𝒜 (ProjectiveUnitOpen.norm_mem b) _
      (fromZeroRingHom 𝒜 _ (ProjSpace.grad0Equiv R n r)) =
    awayMap 𝒜 (ProjSpace.X_mem_one R n j) _
      (fromZeroRingHom 𝒜 _ (ProjSpace.grad0Equiv R n r))
  rw [awayMap_fromZeroRingHom, awayMap_fromZeroRingHom]

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Extend a point of the norm open across the coordinate overlap when its
chart function is invertible. -/
def intersectionPoint (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) : Intersection b j →+* S :=
  IsLocalization.Away.lift (chartElement b j) (g := f.toRingHom) hj

theorem intersectionPoint_fromNorm (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j)))
    (z : ProjectiveUnitOpen.CoordinateRing b) :
    intersectionPoint b f j hj (fromNorm b j z) = f z :=
  IsLocalization.Away.lift_eq (chartElement b j) (g := f.toRingHom) hj z

/-- The standard coordinate-chart point furnished by an actual point of
the norm chart after localizing at a coordinate function. -/
def standardPoint (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) :
    StandardChart (R := R) j →ₐ[R] S where
  __ := (intersectionPoint b f j hj).comp (fromStandard b j)
  commutes' r := by
    change intersectionPoint b f j hj
      (fromStandard b j (algebraMap R (StandardChart (R := R) j) r)) = _
    rw [fromStandard_algebraMap, intersectionPoint_fromNorm, f.commutes]

/-- Coordinates in which the distinguished coordinate is one. -/
def normalizedCoordinates (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) (i : Fin (n + 1)) : S :=
  standardPoint b f j hj (ProjSpace.ratio R n j i)

theorem normalizedCoordinates_self (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) :
    normalizedCoordinates b f j hj j = 1 := by
  rw [normalizedCoordinates, ProjSpace.ratio_self, map_one]

/-- Evaluation at the standard ratios is the actual homogeneous fraction
with the distinguished coordinate as denominator. -/
theorem aeval_ratio_of_isHomogeneous (j : Fin (n + 1))
    (p : P) {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (ProjSpace.ratio R n j) p =
      Away.mk 𝒜 (ProjSpace.X_mem_one R n j) d p
        (by simpa only [smul_eq_mul, mul_one] using
          (MvPolynomial.mem_homogeneousSubmodule d p).mpr hp) := by
  apply HomogeneousLocalization.val_injective
  change algebraMap (StandardChart (R := R) j) (Localization.Away (MvPolynomial.X j : P))
    (MvPolynomial.aeval (ProjSpace.ratio R n j) p) = _
  rw [MvPolynomial.map_aeval]
  have hr : (fun i => algebraMap (StandardChart (R := R) j)
      (Localization.Away (MvPolynomial.X j : P)) (ProjSpace.ratio R n j i)) =
      fun i => (IsLocalization.Away.invSelf (MvPolynomial.X j : P) :
          Localization.Away (MvPolynomial.X j : P)) *
        algebraMap P (Localization.Away (MvPolynomial.X j : P)) (MvPolynomial.X i) := by
    funext i
    rw [HomogeneousLocalization.algebraMap_apply, ProjSpace.ratio, Away.val_mk,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
    simp only [pow_one]
    change _ * (IsLocalization.Away.invSelf (MvPolynomial.X j : P) :
      Localization.Away (MvPolynomial.X j : P)) = _
    exact mul_comm _ _
  rw [hr]
  change MvPolynomial.eval₂
    ((algebraMap P (Localization.Away (MvPolynomial.X j : P))).comp MvPolynomial.C)
    (fun i => (IsLocalization.Away.invSelf (MvPolynomial.X j : P) :
        Localization.Away (MvPolynomial.X j : P)) *
      algebraMap P (Localization.Away (MvPolynomial.X j : P)) (MvPolynomial.X i)) p = _
  rw [LinSys.eval₂_mul_of_isHomogeneous _ _ _ hp]
  calc
    _ = IsLocalization.Away.invSelf (MvPolynomial.X j : P) ^ d *
        algebraMap P (Localization.Away (MvPolynomial.X j : P)) p := by
      congr 1
      exact (MvPolynomial.eval₂_comp_left
        (algebraMap P (Localization.Away (MvPolynomial.X j : P)))
        MvPolynomial.C MvPolynomial.X p).symm.trans
          (congrArg (algebraMap P (Localization.Away (MvPolynomial.X j : P)))
            (MvPolynomial.eval₂_eta p))
    _ = _ := by
      rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
      unfold IsLocalization.Away.invSelf
      rw [← IsLocalization.mk'_pow]
      simp only [one_pow]
      exact mul_comm _ _

/-- The normalized coordinates evaluate homogeneous polynomials by the
corresponding standard-chart fraction. -/
theorem aeval_normalizedCoordinates (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j)))
    (p : P) {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (normalizedCoordinates b f j hj) p =
      standardPoint b f j hj
        (Away.mk 𝒜 (ProjSpace.X_mem_one R n j) d p
          (by simpa only [smul_eq_mul, mul_one] using
            (MvPolynomial.mem_homogeneousSubmodule d p).mpr hp)) := by
  rw [← aeval_ratio_of_isHomogeneous j p hp,
    MvPolynomial.comp_aeval_apply]
  rfl

/-- The norm evaluated at the normalized coordinates is the normalized
homogeneous norm function on the standard chart. -/
theorem aeval_normalizedCoordinates_norm
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) :
    MvPolynomial.aeval (normalizedCoordinates b f j hj) N =
      standardPoint b f j hj (standardNorm b j) := by
  rw [aeval_normalizedCoordinates b f j hj N
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp (ProjectiveUnitOpen.norm_mem b))]
  simp only [standardNorm, Away.isLocalizationElem, pow_one]

/-- Every point in a coordinate chart of the projective norm open produces
coordinates of an actual unit of the finite free algebra. -/
theorem isUnit_aeval_normalizedCoordinates_norm
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) :
    IsUnit (MvPolynomial.aeval (normalizedCoordinates b f j hj) N) := by
  rw [aeval_normalizedCoordinates_norm]
  exact (isUnit_fromStandard_standardNorm b j).map (intersectionPoint b f j hj)

/-- The normalized lift is a unit constructed from the standard coordinate
ratios and the proven invertibility of their norm. -/
def normalizedUnit (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) : (S ⊗[R] A)ˣ :=
  ((UnitNormPolynomial.isUnit_aeval_normPolynomial_iff b _).mp
    (isUnit_aeval_normalizedCoordinates_norm b f j hj)).unit

theorem coordinates_normalizedUnit (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) :
    UnitNormPolynomial.coordinates b (normalizedUnit b f j hj : S ⊗[R] A) =
      normalizedCoordinates b f j hj := by
  funext i
  rw [normalizedUnit, IsUnit.unit_spec, UnitNormPolynomial.coordinates_element]

/-- The fractions in the norm chart and in the standard chart satisfy the
actual overlap identity; no quotient universal property is assumed. -/
theorem overlap_fraction (j : Fin (n + 1)) (m : ℕ) (p : P)
    (hp : p ∈ 𝒜 (m • (n + 1))) :
    fromStandard b j (standardNorm b j) ^ m *
        fromNorm b j (Away.mk 𝒜 (ProjectiveUnitOpen.norm_mem b) m p hp) =
      fromStandard b j (Away.mk 𝒜 (ProjSpace.X_mem_one R n j) (m * (n + 1)) p
        (by simpa only [smul_eq_mul, mul_one] using hp)) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    fromStandard, fromNorm, standardNorm, Away.isLocalizationElem, pow_one,
    awayMap_mk, Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

/-- Evaluating an explicit norm fraction clears its actual denominator. -/
theorem projectivePoint_mk (a : (S ⊗[R] A)ˣ) (m : ℕ) (p : P)
    (hp : p ∈ 𝒜 (m • (n + 1))) :
    MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) N ^ m *
        ProjectiveUnitOpen.projectivePoint b a
          (Away.mk 𝒜 (ProjectiveUnitOpen.norm_mem b) m p hp) =
      MvPolynomial.aeval (UnitNormPolynomial.coordinates b (a : S ⊗[R] A)) p := by
  have h : algebraMap P (UnitNormPolynomial.CoordinateRing b) (N ^ m) *
      algebraMap (ProjectiveUnitOpen.CoordinateRing b) (UnitNormPolynomial.CoordinateRing b)
        (Away.mk 𝒜 (ProjectiveUnitOpen.norm_mem b) m p hp) =
      algebraMap P (UnitNormPolynomial.CoordinateRing b) p := by
    rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec' (UnitNormPolynomial.CoordinateRing b) p
      (⟨N ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers N)
  have h' := congrArg (UnitNormPolynomial.unitToHom b a) h
  simp only [ProjectiveUnitOpen.projectivePoint, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  simpa only [map_mul, UnitNormPolynomial.unitToHom_algebraMap, map_pow] using h'

/-- The normalized unit maps back to the prescribed point of the projective
norm open whenever the displayed chart function is invertible. -/
theorem projectivePoint_normalizedUnit
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (chartElement b j))) :
    ProjectiveUnitOpen.projectivePoint b (normalizedUnit b f j hj) = f.toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective 𝒜 (ProjectiveUnitOpen.norm_mem b) z
  apply ((isUnit_aeval_normalizedCoordinates_norm b f j hj).pow m).mul_left_cancel
  have h := congrArg (intersectionPoint b f j hj) (overlap_fraction b j m p hp)
  rw [map_mul, map_pow, intersectionPoint_fromNorm] at h
  change standardPoint b f j hj (standardNorm b j) ^ m * f _ =
    standardPoint b f j hj _ at h
  have hp' : p.IsHomogeneous (m * (n + 1)) := by
    simpa only [smul_eq_mul] using (MvPolynomial.mem_homogeneousSubmodule _ _).mp hp
  rw [← aeval_normalizedCoordinates_norm,
    ← aeval_normalizedCoordinates b f j hj p hp'] at h
  have h' := projectivePoint_mk b (normalizedUnit b f j hj) m p hp
  rw [coordinates_normalizedUnit] at h'
  exact h'.trans h.symm

end SchemeTheory.Affine.ProjectiveUnitCharts
