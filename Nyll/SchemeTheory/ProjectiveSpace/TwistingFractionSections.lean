/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingFractionCoefficients
import Nyll.SchemeTheory.ProjectiveSpace.UnitFractionEvaluation
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteUnitClosedImmersionProj
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Sheaves.FrameSectionEquivalence
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.Finset.Max

/-!
# Actual twisting-sheaf sections as shifted homogeneous fractions

The computed fraction coefficients multiply the actual coordinate
frames of `O(d)`. Their change-of-coordinate equation cancels the frame
transition, so the resulting section is independent of the coordinate.
This gives an actual linear equivalence on every nonempty coordinate
intersection, compatible with the original sheaf restrictions.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjSpace

open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
open ProjSpaceCech Scheme.Modules Scheme.Modules.GlueOfCocycle

attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem coordinateIntersection_mono {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    coordinateIntersection R n J ≤ coordinateIntersection R n I := by
  change (𝟙 (Proj 𝒜)) ⁻¹ᵁ coordinateIntersection R n J ≤
    (𝟙 (Proj 𝒜)) ⁻¹ᵁ coordinateIntersection R n I
  rw [← ClosedImmCech.finsetInf_basicOpen (𝟙 (Proj 𝒜)),
    ← ClosedImmCech.finsetInf_basicOpen (𝟙 (Proj 𝒜))]
  exact biInf_mono hIJ

/-- A coordinate frame identifies shifted homogeneous fractions with
the actual sections of the native twisting sheaf on the intersection. -/
def twistingFractionSectionEquivAt (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I) :
    GradedModule.sec (GradedModule.FD R n d) I ≃ₗ[R]
      sectionModuleOverBase ((𝟙 (Proj 𝒜)) ≫ π R n)
        ((twistingSheaf R n).tensorPow d) (coordinateIntersection R n I) := by
  let hs := (isFrameOn_twistingCoordinateSection R n i).tensorPowSection_monoidalV2 d
  exact (twistingFractionCoefficientEquiv R n d i hi).trans
    (hs.sectionEquivOverBase ((𝟙 (Proj 𝒜)) ≫ π R n) le_top
      (coordinateIntersection_le_standardOpen R n hi))

theorem twistingFractionSectionEquivAt_apply (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n d) I) :
    twistingFractionSectionEquivAt R n d i hi z =
      (show Γ(Proj 𝒜, coordinateIntersection R n I) from
        twistingFractionCoefficientEquiv R n d i hi z) •
        ((twistingSheaf R n).tensorPow d).presheaf.map
          (homOfLE (le_top : coordinateIntersection R n I ≤ ⊤)).op
          (tensorPowSection (twistingCoordinateSection R n i) d) := rfl

/-- The actual section does not depend on which inverted coordinate
was used to trivialize the shift. -/
theorem twistingFractionSectionEquivAt_independent (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) (hj : j ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n d) I) :
    twistingFractionSectionEquivAt R n d i hi z =
      twistingFractionSectionEquivAt R n d j hj z := by
  let M : (Proj 𝒜).Modules := (twistingSheaf R n).tensorPow d
  let V : (Proj 𝒜).Opens := coordinateIntersection R n I
  let hVi : V ≤ standardOpen R n i := coordinateIntersection_le_standardOpen R n hi
  let si : Γ(M, ⊤) := tensorPowSection (twistingCoordinateSection R n i) d
  let sj : Γ(M, ⊤) := tensorPowSection (twistingCoordinateSection R n j) d
  have hframe : rO hVi (coordinateRatioSection R n i j) ^ d •
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op si =
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op sj := by
    have h := congrArg (fun s : Γ(M, standardOpen R n i) =>
      M.presheaf.map (homOfLE hVi).op s)
      (coordinateRatioSection_pow_smul_twistingCoordinateSection R n d i j)
    change M.presheaf.map (homOfLE hVi).op
        (coordinateRatioSection R n i j ^ d •
          M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op si) =
      M.presheaf.map (homOfLE hVi).op
        (M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op sj) at h
    rw [M.map_smul, map_pow, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
      ← M.presheaf.map_comp] at h
    exact h
  rw [twistingFractionSectionEquivAt_apply, twistingFractionSectionEquivAt_apply]
  change (show Γ(Proj 𝒜, V) from twistingFractionCoefficientEquiv R n d i hi z) •
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op si =
    (show Γ(Proj 𝒜, V) from twistingFractionCoefficientEquiv R n d j hj z) •
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op sj
  rw [twistingFractionCoefficientEquiv_transition R n d i hi j hj z,
    mul_comm (rO hVi (coordinateRatioSection R n i j) ^ d), mul_smul, hframe]

/-- With one fixed coordinate, the actual section comparison commutes
with the original native sheaf restriction. -/
theorem twistingFractionSectionEquivAt_restrict (d : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (i : Fin (n + 1)) (hi : i ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n d) I) :
    sectionRestrictionOverBase ((𝟙 (Proj 𝒜)) ≫ π R n)
        ((twistingSheaf R n).tensorPow d) (coordinateIntersection_mono R n hIJ)
        (twistingFractionSectionEquivAt R n d i hi z) =
      twistingFractionSectionEquivAt R n d i (hIJ hi)
        (GradedModule.secIncl _ hIJ z) := by
  let hs := (isFrameOn_twistingCoordinateSection R n i).tensorPowSection_monoidalV2 d
  change sectionRestrictionOverBase ((𝟙 (Proj 𝒜)) ≫ π R n)
      ((twistingSheaf R n).tensorPow d) (coordinateIntersection_mono R n hIJ)
      (hs.sectionEquivOverBase ((𝟙 (Proj 𝒜)) ≫ π R n) le_top
        (coordinateIntersection_le_standardOpen R n hi)
        (twistingFractionCoefficientEquiv R n d i hi z)) =
    hs.sectionEquivOverBase ((𝟙 (Proj 𝒜)) ≫ π R n) le_top
      (coordinateIntersection_le_standardOpen R n (hIJ hi))
      (twistingFractionCoefficientEquiv R n d i (hIJ hi) (GradedModule.secIncl _ hIJ z))
  rw [IsFrameOn.sectionEquivOverBase_restrict]
  exact congrArg (hs.sectionEquivOverBase ((𝟙 (Proj 𝒜)) ≫ π R n) le_top
    (coordinateIntersection_le_standardOpen R n (hIJ hi)))
    (twistingFractionCoefficientEquiv_restrict R n d hIJ i hi z).symm

/-- The actual section equivalence on a nonempty coordinate intersection.
The least coordinate only supplies a frame; the resulting map is independent of it. -/
def twistingFractionSectionEquiv (d : ℕ)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    GradedModule.sec (GradedModule.FD R n d) I ≃ₗ[R]
      sectionModuleOverBase ((𝟙 (Proj 𝒜)) ≫ π R n)
        ((twistingSheaf R n).tensorPow d) (coordinateIntersection R n I) :=
  twistingFractionSectionEquivAt R n d (I.min' hI) (Finset.min'_mem I hI)

/-- Enlarging the coordinate intersection index agrees with native
restriction, even when the chosen least coordinate changes. -/
theorem twistingFractionSectionEquiv_restrict (d : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) (hI : I.Nonempty)
    (z : GradedModule.sec (GradedModule.FD R n d) I) :
    sectionRestrictionOverBase ((𝟙 (Proj 𝒜)) ≫ π R n)
        ((twistingSheaf R n).tensorPow d) (coordinateIntersection_mono R n hIJ)
        (twistingFractionSectionEquiv R n d I hI z) =
      twistingFractionSectionEquiv R n d J (hI.mono hIJ)
        (GradedModule.secIncl _ hIJ z) :=
  (twistingFractionSectionEquivAt_restrict R n d hIJ
    (I.min' hI) (Finset.min'_mem I hI) z).trans
    (twistingFractionSectionEquivAt_independent R n d
      (I.min' hI) (hIJ (Finset.min'_mem I hI))
      (J.min' (hI.mono hIJ)) (Finset.min'_mem J (hI.mono hIJ))
      (GradedModule.secIncl _ hIJ z))

end AlgebraicGeometry.ProjSpace
