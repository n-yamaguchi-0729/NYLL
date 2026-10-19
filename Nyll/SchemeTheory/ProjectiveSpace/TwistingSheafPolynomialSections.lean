/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Actual twisting-sheaf sections of homogeneous polynomials

The regular coefficients `p / X i ^ d`, multiplied by the `d`-th power
of the actual coordinate frame, agree on overlaps. Gluing gives a native
global section of `O(d)`. Its exact restriction formula proves additivity
and injectivity over every coefficient ring. Surjectivity is not assumed
in this construction.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev res {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    Γ(M, U) →+ Γ(M, V) := (M.presheaf.map (homOfLE h).op).hom

private theorem res_res {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(M, U)) :
    res M hWV (res M hVU s) = res M (hWV.trans hVU) s := by
  change (M.presheaf.map (homOfLE hVU).op ≫
    M.presheaf.map (homOfLE hWV).op).hom s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private theorem res_smul {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (r : Γ(X, U)) (s : Γ(M, U)) :
    res M h (r • s) = rO h r • res M h s := M.map_smul (homOfLE h) r s

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Powers of the coordinate sections have the corresponding powered
transition function on the actual standard chart. -/
theorem coordinateRatioSection_pow_smul_twistingCoordinateSection
    (d : ℕ) (i j : Fin (n + 1)) :
    coordinateRatioSection R n i j ^ d •
        ((twistingSheaf R n).tensorPow d).presheaf.map
          (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
          (tensorPowSection (twistingCoordinateSection R n i) d) =
      ((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
        (tensorPowSection (twistingCoordinateSection R n j) d) := by
  rw [map_tensorPowSection, map_tensorPowSection, ← tensorPowSection_smul]
  exact congrArg (fun s : Γ(twistingSheaf R n, standardOpen R n i) =>
    tensorPowSection s d) (coordinateRatioSection_smul_twistingCoordinateSection R n i j)

/-- The local twisting-sheaf section represented by a homogeneous polynomial. -/
def homogeneousTwistingLocalSection (d : ℕ) (p : 𝒜 d) (i : Fin (n + 1)) :
    Γ((twistingSheaf R n).tensorPow d, standardOpen R n i) :=
  homogeneousRatioSection R n d p i •
    ((twistingSheaf R n).tensorPow d).presheaf.map
      (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
      (tensorPowSection (twistingCoordinateSection R n i) d)

private theorem localSection_compatible (d : ℕ) (p : 𝒜 d) (i j : Fin (n + 1)) :
    ((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE (inf_le_left : standardOpen R n i ⊓ standardOpen R n j ≤
          standardOpen R n i)).op (homogeneousTwistingLocalSection R n d p i) =
      ((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE inf_le_right).op (homogeneousTwistingLocalSection R n d p j) := by
  let M : (Proj 𝒜).Modules := (twistingSheaf R n).tensorPow d
  let V : (Proj 𝒜).Opens := standardOpen R n i ⊓ standardOpen R n j
  have hframe := congrArg (res M (inf_le_left : V ≤ standardOpen R n i))
    (coordinateRatioSection_pow_smul_twistingCoordinateSection R n d i j)
  change res M inf_le_left
      (coordinateRatioSection R n i j ^ d • res M le_top
        (tensorPowSection (twistingCoordinateSection R n i) d)) =
    res M inf_le_left (res M le_top
      (tensorPowSection (twistingCoordinateSection R n j) d)) at hframe
  rw [res_smul, map_pow, res_res, res_res] at hframe
  change res M inf_le_left (homogeneousRatioSection R n d p i • res M le_top
      (tensorPowSection (twistingCoordinateSection R n i) d)) =
    res M inf_le_right (homogeneousRatioSection R n d p j • res M le_top
      (tensorPowSection (twistingCoordinateSection R n j) d))
  rw [res_smul, res_smul, res_res, res_res,
    homogeneousRatioSection_transition R n d p i j inf_le_left inf_le_right,
    mul_comm (rO (inf_le_left : V ≤ standardOpen R n i)
      (coordinateRatioSection R n i j) ^ d), mul_smul, hframe]

/-- The local polynomial sections glue in the actual tensor power sheaf. -/
theorem exists_polynomialTwistingSection (d : ℕ) (p : 𝒜 d) :
    ∃ s : Γ((twistingSheaf R n).tensorPow d, ⊤), ∀ i : Fin (n + 1),
      ((twistingSheaf R n).tensorPow d).presheaf.map
          (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op s =
        homogeneousTwistingLocalSection R n d p i := by
  obtain ⟨s, hs⟩ := (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    ((twistingSheaf R n).tensorPow d) (twistingCover R n) ⊤
    (fun _ => le_top) (iSup_twistingCover R n).ge).2
      (fun i => homogeneousTwistingLocalSection R n d p i.down)
      (fun i j => localSection_compatible R n d p i.down j.down)
  exact ⟨s, fun i => hs (ULift.up i)⟩

/-- The actual global section of `O(d)` represented by a homogeneous
polynomial, constructed by gluing its regular chart expressions. -/
def polynomialTwistingSection (d : ℕ) (p : 𝒜 d) :
    Γ((twistingSheaf R n).tensorPow d, ⊤) :=
  (exists_polynomialTwistingSection R n d p).choose

/-- The constructed section retains its precise polynomial chart expression. -/
theorem polynomialTwistingSection_restrict (d : ℕ) (p : 𝒜 d) (i : Fin (n + 1)) :
    ((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
        (polynomialTwistingSection R n d p) =
      homogeneousTwistingLocalSection R n d p i :=
  (exists_polynomialTwistingSection R n d p).choose_spec i

theorem polynomialTwistingSection_zero (d : ℕ) :
    polynomialTwistingSection R n d 0 = 0 := by
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    ((twistingSheaf R n).tensorPow d) (twistingCover R n) ⊤
    (fun _ => le_top) (iSup_twistingCover R n).ge).1
  intro i
  rw [map_zero, polynomialTwistingSection_restrict, homogeneousTwistingLocalSection,
    homogeneousRatioSection_zero, zero_smul]

theorem polynomialTwistingSection_add (d : ℕ) (p q : 𝒜 d) :
    polynomialTwistingSection R n d (p + q) =
      polynomialTwistingSection R n d p + polynomialTwistingSection R n d q := by
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    ((twistingSheaf R n).tensorPow d) (twistingCover R n) ⊤
    (fun _ => le_top) (iSup_twistingCover R n).ge).1
  intro i
  rw [map_add, polynomialTwistingSection_restrict, polynomialTwistingSection_restrict,
    polynomialTwistingSection_restrict, homogeneousTwistingLocalSection,
    homogeneousTwistingLocalSection, homogeneousTwistingLocalSection,
    homogeneousRatioSection_add, add_smul]

/-- The additive map from homogeneous polynomials to actual twisting-sheaf
global sections. -/
def polynomialTwistingSectionAddHom (d : ℕ) :
    𝒜 d →+ Γ((twistingSheaf R n).tensorPow d, ⊤) where
  toFun p := polynomialTwistingSection R n d p
  map_zero' := polynomialTwistingSection_zero R n d
  map_add' p q := polynomialTwistingSection_add R n d p q

/-- The actual global polynomial-section map is injective over an
arbitrary coefficient ring. -/
theorem polynomialTwistingSection_injective (d : ℕ) :
    Function.Injective (polynomialTwistingSection R n d) := by
  intro p q hpq
  have h := congrArg
    (res ((twistingSheaf R n).tensorPow d)
      (le_top : standardOpen R n 0 ≤ ⊤)) hpq
  change ((twistingSheaf R n).tensorPow d).presheaf.map _
      (polynomialTwistingSection R n d p) =
    ((twistingSheaf R n).tensorPow d).presheaf.map _
      (polynomialTwistingSection R n d q) at h
  rw [polynomialTwistingSection_restrict, polynomialTwistingSection_restrict] at h
  exact homogeneousRatioSection_injective R n d 0
    ((((isFrameOn_twistingCoordinateSection R n 0).tensorPowSection_monoidalV2 d)
      le_top le_rfl).1 h)

end AlgebraicGeometry.ProjSpace
