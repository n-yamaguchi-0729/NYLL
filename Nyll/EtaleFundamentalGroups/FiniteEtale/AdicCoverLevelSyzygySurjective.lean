/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygySections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.LocalMorphisms
public import Nyll.SchemeTheory.Modules.Sections.AffineEpi
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleExactness
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sets.Opens

/-!
# Surjectivity of the original native syzygy transitions

The local frames of the original invertible sheaf give an affine cover
on which the actual syzygy transition is surjective. This proves that
the native sheaf transition is epimorphic. Quasicoherence then proves
surjectivity on every affine open, without choosing a frame there.

These are the original kernels of the closed-level presentations. The
result does not assert surjectivity on global sections of a proper scheme;
that further step requires a cohomological vanishing argument.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) [(L.tensorPow d).IsQuasicoherent]
  (K : Type u) [Finite K]
  (α : ∀ n : ℕ, (show X.Modules from SheafOfModules.free K) ⟶
    moduleSheaf f I V n ⊗ L.tensorPow d)
  (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L.tensorPow d) = α n)

/-- The actual native syzygy transition is epimorphic. The proof derives
local lifts from the original invertible sheaf, without a supplied frame. -/
theorem levelPresentationKernelTransition_epi (hL : IsInvertible L)
    (n : ℕ) (hgen : Epi (α (n + 1))) :
    Epi (levelPresentationKernelTransition f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) α hα n) := by
  let q := levelPresentationKernelTransition f I V (L.tensorPow d)
    (show X.Modules from SheafOfModules.free K) α hα n
  let M := levelPresentationKernel f I V (L.tensorPow d)
    (show X.Modules from SheafOfModules.free K) n (α n)
  obtain ⟨C, t, ht, hcover⟩ := hL.exists_frame_cover
  apply (Hom.epi_iff_locallySurjective q).mpr
  intro U z x hx
  have hxC : x ∈ ⨆ i : X, C i := by
    rw [hcover]
    exact Set.mem_univ x
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxC
  obtain ⟨W, hW, hxW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ U ⊓ C i from ⟨hx, hxi⟩)
  have hWC : W ≤ C i := hWU.trans inf_le_right
  have hWU' : W ≤ U := hWU.trans inf_le_left
  let s : Γ(L.tensorPow d, W) :=
    (L.tensorPow d).presheaf.map (homOfLE hWC).op (tensorPowSection (t i) d)
  have hs : IsFrameOn s W :=
    (((ht i).tensorPowSection_monoidalV2 d).map (homOfLE hWC)).mono hWC
  have hsurj : Function.Surjective (q.app W) :=
    levelPresentationKernelTransition_app_surjective f I K ⟨W, hW⟩ V L d α s hs hα hL n hgen
  obtain ⟨y, hy⟩ := hsurj (M.presheaf.map (homOfLE hWU').op z)
  exact ⟨W, hWU', hxW, y, hy⟩

/-- Every affine open has surjective original native syzygy section maps,
including opens on which the chosen invertible sheaf has no supplied frame. -/
theorem levelPresentationKernelTransition_app_surjective_of_isAffineOpen
    (hL : IsInvertible L) (n : ℕ) (hgen : Epi (α (n + 1)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective
      ((levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα n).app U) := by
  have : Epi (levelPresentationKernelTransition f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) α hα n) :=
    levelPresentationKernelTransition_epi f I V L d K α hα hL n hgen
  exact Hom.app_surjective_of_epi_of_isAffineOpen
    (levelPresentationKernelTransition f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) α hα n) U hU

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
