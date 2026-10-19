/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Nyll.SchemeTheory.Modules.Descent.UnitCocycleTrivializations
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.ProjectivePresentation.ProjectivePresentation
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Recovering the twisting sheaf from its coordinate presentation

The frame and coordinate-ratio equations of an actual projective
presentation over the identity give the transition functions of the
constructed twisting sheaf. Gluing these frames therefore recovers
the sheaf, with its original coordinate sections. In particular, this
can be applied to the presentation constructed by coefficient base
change; no isomorphism of the sheaves is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem restrict_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE hWV).op (M.presheaf.map (homOfLE hVU).op s) =
      M.presheaf.map (homOfLE (hWV.trans hVU)).op s := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

private theorem app_restrict {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (hVU : V ≤ U) (s : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE hVU).op s) =
      N.presheaf.map (homOfLE hVU).op (φ.app U s) := by
  exact congrArg (fun a : Γ(M, U) ⟶ Γ(N, V) => a.hom s)
    (φ.mapPresheaf.naturality (homOfLE hVU).op)

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

private theorem presentation_identity_ratio (M : (Proj 𝒜).Modules)
    (P : M.ProjPresentation (π R n) n) (hP : P.toProj = 𝟙 (Proj 𝒜))
    (i j : Fin (n + 1)) :
    coordinateRatioSection R n i j •
        M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (P.σ i) =
      M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (P.σ j) := by
  have h := P.app_ratio_smul i j
  rw [hP] at h
  let U : (Proj 𝒜).Opens := standardOpen R n i
  let a : Γ(Proj 𝒜, U) := coordinateRatioSection R n i j
  let b : Γ(Proj 𝒜, U) := ((𝟙 (Proj 𝒜)).app U).hom a
  have hid : b = a :=
    (congrArg (fun φ : Γ(Proj 𝒜, U) ⟶ Γ(Proj 𝒜, U) => φ.hom a)
      (Scheme.Hom.id_app U)).trans (CommRingCat.id_apply Γ(Proj 𝒜, U) a)
  have h' : b •
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (P.σ i) =
    M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (P.σ j) := h
  exact (congrArg (fun b : Γ(Proj 𝒜, U) =>
    b • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (P.σ i)) hid.symm).trans h'

private theorem presentation_identity_frame (M : (Proj 𝒜).Modules)
    (P : M.ProjPresentation (π R n) n) (hP : P.toProj = 𝟙 (Proj 𝒜))
    (i : Fin (n + 1)) : IsFrameOn (P.σ i) (standardOpen R n i) := by
  intro V hVtop hVi
  have h := P.frame i V
  rw [hP] at h
  exact h hVi

/-- Coordinate frames of a presentation over the identity determine an
isomorphism to the actual twisting sheaf, including its global sections. -/
theorem exists_iso_twistingSheaf_of_identity_presentation (M : (Proj 𝒜).Modules)
    (P : M.ProjPresentation (π R n) n) (hP : P.toProj = 𝟙 (Proj 𝒜)) :
    ∃ e : M ≅ twistingSheaf R n,
      ∀ i : Fin (n + 1), e.hom.app ⊤ (P.σ i) = twistingCoordinateSection R n i := by
  let U : ULift.{u} (Fin (n + 1)) → (Proj 𝒜).Opens := twistingCover R n
  let s : ∀ i : ULift.{u} (Fin (n + 1)), Γ(M, U i) := fun i =>
    M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (P.σ i.down)
  have hs : ∀ i : ULift.{u} (Fin (n + 1)), IsFrameOn (s i) (U i) := fun i =>
    (presentation_identity_frame R n M P hP i.down).map
      (homOfLE (le_top : U i ≤ ⊤))
  have htrans : ∀ i j : ULift.{u} (Fin (n + 1)),
      M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j) =
        (twistingCocycle R n).u i j •
          M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i) := by
    intro i j
    have h := congrArg
      (M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op)
      (presentation_identity_ratio R n M P hP i.down j.down)
    rw [Scheme.Modules.map_smul, restrict_restrict, restrict_restrict] at h
    change M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op
        (M.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (P.σ j.down)) =
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
        (coordinateRatioSection R n i.down j.down) •
        M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
          (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (P.σ i.down))
    rw [restrict_restrict, restrict_restrict]
    exact h.symm
  obtain ⟨e, he⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame
    (iSup_twistingCover R n) (twistingCocycle R n) s hs htrans
  refine ⟨e, ?_⟩
  intro j
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    (twistingSheaf R n) U ⊤ (fun _ => le_top) (iSup_twistingCover R n).ge).1
  intro i
  calc
    (twistingSheaf R n).presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
        (e.hom.app ⊤ (P.σ j)) =
        e.hom.app (U i) (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (P.σ j)) :=
      (app_restrict e.hom le_top (P.σ j)).symm
    _ = e.hom.app (U i) (coordinateRatioSection R n i.down j • s i) :=
      congrArg (e.hom.app (U i)) (presentation_identity_ratio R n M P hP i.down j).symm
    _ = coordinateRatioSection R n i.down j • e.hom.app (U i) (s i) :=
      Scheme.Modules.Hom.app_smul e.hom (coordinateRatioSection R n i.down j) (s i)
    _ = coordinateRatioSection R n i.down j • glueFrame (twistingCocycle R n) i :=
      congrArg (fun z : Γ(twistingSheaf R n, U i) =>
        coordinateRatioSection R n i.down j • z) (he i)
    _ = coordinateRatioSection R n i.down j •
        (twistingSheaf R n).presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
          (twistingCoordinateSection R n i.down) :=
      congrArg (fun z : Γ(twistingSheaf R n, U i) =>
        coordinateRatioSection R n i.down j • z)
          (twistingCoordinateSection_restrict_self R n i.down).symm
    _ = (twistingSheaf R n).presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
        (twistingCoordinateSection R n j) :=
      coordinateRatioSection_smul_twistingCoordinateSection R n i.down j

end AlgebraicGeometry.ProjSpace
