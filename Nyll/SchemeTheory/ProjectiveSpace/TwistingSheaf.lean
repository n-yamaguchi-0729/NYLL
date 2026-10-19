/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackIsoUnit
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.ProjectivePresentation.ProjectivePresentation
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme

/-!
# The twisting sheaf and its coordinate sections

The coordinate cocycle is glued as an actual sheaf of modules. Its
global coordinate section `X k` has component `X k / X i` on the
`i`-th standard chart. The corresponding local frame is identified
with the one supplied by sheaf gluing, proving local invertibility.

These sections give the native projective presentation whose map to
projective space is the identity. This supplies the line bundle and
its actual coordinate sections used in subsequent denominator
clearing arguments; no graded presentation of an arbitrary coherent
sheaf is assumed or asserted here.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The sheaf `𝒪(1)` obtained by gluing the coordinate unit cocycle. -/
abbrev twistingSheaf : (Proj 𝒜).Modules := glueOfCocycle (twistingCocycle R n)

/-- The global coordinate section with local component `X k / X i`. -/
def twistingCoordinateSection (k : Fin (n + 1)) : Γ(twistingSheaf R n, ⊤) :=
  glueMk (twistingCocycle R n) ⊤
    (fun i => rO inf_le_right (coordinateRatioSection R n i.down k)) (by
      intro i j
      change rO (leTi (U := twistingCover R n) ⊤ i j)
          (rO inf_le_right (coordinateRatioSection R n i.down k)) =
        rO (leij (U := twistingCover R n) ⊤ i j)
          (rO inf_le_left (coordinateRatioSection R n i.down j.down)) *
        rO (leTj (U := twistingCover R n) ⊤ i j)
          (rO inf_le_right (coordinateRatioSection R n j.down k))
      rw [rO_rO, rO_rO, rO_rO]
      exact (coordinateRatioSection_mul R n i.down j.down k _ _).symm)

/-- Every restriction of a coordinate section has the expected literal
coordinate ratio as its component. -/
theorem twistingCoordinateSection_restrict_component (k : Fin (n + 1))
    (V : (Proj 𝒜).Opens) (i : ULift.{u} (Fin (n + 1))) :
    glueComponent (twistingCocycle R n) V i
        ((twistingSheaf R n).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          (twistingCoordinateSection R n k)) =
      rO inf_le_right (coordinateRatioSection R n i.down k) := by
  change rO (inf_le_inf_right (twistingCover R n i) (le_top : V ≤ ⊤))
    (rO inf_le_right (coordinateRatioSection R n i.down k)) = _
  rw [rO_rO]

/-- The matching coordinate restricts to the local frame supplied by gluing. -/
theorem twistingCoordinateSection_restrict_self (i : Fin (n + 1)) :
    (twistingSheaf R n).presheaf.map
        (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
        (twistingCoordinateSection R n i) =
      glueFrame (twistingCocycle R n) (ULift.up i) := by
  apply glue_ext
  intro k
  rw [twistingCoordinateSection_restrict_component, glueComponent_glueFrame]
  change rO inf_le_right (coordinateRatioSection R n k.down i) =
    rO (le_of_eq (inf_comm (standardOpen R n i) (twistingCover R n k)))
      (rO inf_le_left (coordinateRatioSection R n k.down i))
  rw [rO_rO]

/-- On its standard chart a coordinate section freely generates all
sections on every smaller open. -/
theorem isFrameOn_twistingCoordinateSection (i : Fin (n + 1)) :
    IsFrameOn (twistingCoordinateSection R n i) (standardOpen R n i) := by
  intro V hVtop hVi
  have hframe := isFrameOn_glueFrame (twistingCocycle R n) (ULift.up i) hVi hVi
  have hres : (twistingSheaf R n).presheaf.map (homOfLE hVi).op
      (glueFrame (twistingCocycle R n) (ULift.up i)) =
    (twistingSheaf R n).presheaf.map (homOfLE hVtop).op
      (twistingCoordinateSection R n i) := by
    rw [← twistingCoordinateSection_restrict_self]
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
    rfl
  simpa only [hres] using hframe

/-- The coordinate-ratio equation holds for the constructed global sections. -/
theorem coordinateRatioSection_smul_twistingCoordinateSection (i j : Fin (n + 1)) :
    coordinateRatioSection R n i j •
        (twistingSheaf R n).presheaf.map
          (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
          (twistingCoordinateSection R n i) =
      (twistingSheaf R n).presheaf.map
        (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
        (twistingCoordinateSection R n j) := by
  apply glue_ext
  intro k
  rw [glueComponent_smul, twistingCoordinateSection_restrict_component,
    twistingCoordinateSection_restrict_component, mul_comm]
  exact coordinateRatioSection_mul R n k.down i j inf_le_right inf_le_left

/-- The glued twisting sheaf is locally isomorphic to the unit module. -/
theorem isInvertible_twistingSheaf : IsInvertible (twistingSheaf R n) := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ ⨆ i, twistingCover R n i := by
    rw [iSup_twistingCover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨twistingCover R n i, hi, ?_⟩
  exact (isFrameOn_glueFrame (twistingCocycle R n) i).nonempty_pullback_iso_unit
    (twistingCover R n i) le_rfl le_rfl

/-- The coordinate sections present the identity map of projective space. -/
def twistingSheafPresentation : (twistingSheaf R n).ProjPresentation (π R n) n where
  σ := twistingCoordinateSection R n
  toProj := 𝟙 (Proj 𝒜)
  toProj_π := Category.id_comp (π R n)
  frame i V hV := isFrameOn_twistingCoordinateSection R n i (le_top : V ≤ ⊤) hV
  app_ratio_smul i j := coordinateRatioSection_smul_twistingCoordinateSection R n i j

end AlgebraicGeometry.ProjSpace
