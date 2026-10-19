/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteSections
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Sections.GlobalGeneratingSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorWithFrame
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Data.Fintype.Sigma
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Actual eventual global generation on projective space

A finite-type quasicoherent module admits native finite generating
sections after every sufficiently large nonnegative twist. The sections
are the extensions of finite affine generators constructed by clearing
coordinate denominators. Tensoring with a coordinate frame identifies the
original affine section module with its twist, so the extended sections
span on that chart. The native free-sheaf morphism is then epimorphic.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Every sufficiently large twist of a finite-type quasicoherent module
on projective space has actual finite global generating sections. -/
theorem exists_twisting_bound_generatingSections (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf) F] :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : (F ⊗ (twistingSheaf R n).tensorPow d).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨r, s, hs, N, hN⟩ := exists_finite_generators_twisting_extensions R n F
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨z, hz⟩ := hN d hd
  let M : (Proj 𝒜).Modules := F ⊗ (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) M :=
    isQuasicoherent_tensor_twistingSheaf R n F d
  let I : Type u := ULift.{u} (Σ i : Fin (n + 1), Fin (r i))
  let t : I → Γ(M, ⊤) := fun a => z a.down.1 a.down.2
  have hspan : ∀ i : ULift.{u} (Fin (n + 1)),
      Submodule.span Γ(Proj 𝒜, twistingCover R n i)
        (Set.range (fun a : I => M.presheaf.map
          (homOfLE (le_top : twistingCover R n i ≤ ⊤)).op (t a))) = ⊤ := by
    intro i
    let c : Γ((twistingSheaf R n).tensorPow d, twistingCover R n i) :=
      ((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE (le_top : twistingCover R n i ≤ ⊤)).op
        (tensorPowSection (twistingCoordinateSection R n i.down) d)
    let l : Γ(F, twistingCover R n i) →ₗ[Γ(Proj 𝒜, twistingCover R n i)]
        Γ(M, twistingCover R n i) :=
      { toFun := fun m => tensorSections m c
        map_add' := fun m m' => tensorSections_add_left m m' c
        map_smul' := fun a m => tensorSections_smul_left a m c }
    have hl : Function.Surjective l :=
      (IsFrameOn.bijective_tensorSections F
        ((isFrameOn_twistingCoordinateSection R n i.down).tensorPowSection_monoidalV2 d)
        le_top le_rfl).2
    let P : Submodule Γ(Proj 𝒜, twistingCover R n i) Γ(M, twistingCover R n i) :=
      Submodule.span Γ(Proj 𝒜, twistingCover R n i)
        (Set.range (fun a : I => M.presheaf.map
          (homOfLE (le_top : twistingCover R n i ≤ ⊤)).op (t a)))
    have hgen : Submodule.span Γ(Proj 𝒜, twistingCover R n i)
        (Set.range (s i.down)) ≤ P.comap l := by
      apply Submodule.span_le.mpr
      rintro m ⟨a, rfl⟩
      change l (s i.down a) ∈ P
      have heq : M.presheaf.map
          (homOfLE (le_top : twistingCover R n i ≤ ⊤)).op
          (t (ULift.up ⟨i.down, a⟩)) = l (s i.down a) := hz i.down a
      rw [← heq]
      exact Submodule.subset_span
        (Set.mem_range_self (show I from ULift.up ⟨i.down, a⟩))
    rw [hs i.down] at hgen
    apply top_unique
    intro y _
    obtain ⟨m, rfl⟩ := hl y
    exact hgen (show m ∈
      (⊤ : Submodule Γ(Proj 𝒜, twistingCover R n i) Γ(F, twistingCover R n i)) from
        Submodule.mem_top)
  have hAffine : ∀ i : ULift.{u} (Fin (n + 1)), IsAffineOpen (twistingCover R n i) :=
    fun i => Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X i.down)
      (X_mem_one R n i.down) one_pos
  refine ⟨generatingSectionsOfAffineSpans M t (twistingCover R n) hAffine
    (iSup_twistingCover R n) hspan, ?_⟩
  exact generatingSectionsOfAffineSpans_isFiniteType M t (twistingCover R n) hAffine
    (iSup_twistingCover R n) hspan

end AlgebraicGeometry.ProjSpace
