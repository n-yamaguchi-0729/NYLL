/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Nyll.SchemeTheory.Modules.Sections.AffineEpi
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorWithFrame
import Nyll.SchemeTheory.RingTheory.LinearAlgebra.NilpotentSurjectivity
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Sets.Opens

/-!
# Nilpotent quotient detection through the original tensor frames

Tensoring sections with an actual frame identifies the original section
modules with their tensor twists. The original whiskered morphism acts
on the first factor. These facts transport kernel containment and ideal
annihilation to the actual twisted section maps.

On a cover by such frames, the nilpotent linear-map criterion detects
epimorphisms from their composite with the original twisted quotient.
Only the untwisted affine kernel and annihilation properties are inputs;
no properties of the twisted kernel or a new comparison are assumed.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private def tensorFrameMap {X : Scheme.{u}} (M : X.Modules) {L : X.Modules}
    {W : X.Opens} (t : Γ(L, W)) : Γ(M, W) →ₗ[Γ(X, W)] Γ(M ⊗ L, W) where
  toFun x := tensorSections x t
  map_add' x y := tensorSections_add_left x y t
  map_smul' a x := tensorSections_smul_left a x t

variable {X : Scheme.{u}} {M N L : X.Modules} {U V W : X.Opens} {s : Γ(L, U)}

/-- The original tensor frame carries the untwisted kernel containment
to the kernel of the original whiskered section map. -/
theorem IsFrameOn.whiskerRight_app_ker_le_smul (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) (q : M ⟶ N) (J : Ideal Γ(X, W))
    (hker : ((q.val.app (op W)).hom).ker ≤
      J • (⊤ : Submodule Γ(X, W) Γ(M, W))) :
    (((q ▷ L).val.app (op W)).hom).ker ≤
      J • (⊤ : Submodule Γ(X, W) Γ(M ⊗ L, W)) := by
  let t : Γ(L, W) := L.presheaf.map (homOfLE hWU).op s
  let lM : Γ(M, W) →ₗ[Γ(X, W)] Γ(M ⊗ L, W) := tensorFrameMap M t
  let lN : Γ(N, W) →ₗ[Γ(X, W)] Γ(N ⊗ L, W) := tensorFrameMap N t
  have hlM : Function.Bijective lM := hs.bijective_tensorSections M hWU hWV
  have hlN : Function.Injective lN := hs.injective_tensorSections N hWU hWV
  intro y hy
  obtain ⟨x, rfl⟩ := hlM.2 y
  have hzero : q.app W x = 0 := by
    apply hlN
    have hnat : (q ▷ L).app W (lM x) = lN (q.app W x) :=
      whiskerRight_app_tensorSections q L x t
    exact hnat.symm.trans ((LinearMap.mem_ker.mp hy).trans lN.map_zero.symm)
  have hx : x ∈ J • (⊤ : Submodule Γ(X, W) Γ(M, W)) :=
    hker (LinearMap.mem_ker.mpr hzero)
  have hmap : (J • (⊤ : Submodule Γ(X, W) Γ(M, W))).map lM ≤
      J • (⊤ : Submodule Γ(X, W) Γ(M ⊗ L, W)) :=
    (Submodule.map_smul'' J (⊤ : Submodule Γ(X, W) Γ(M, W)) lM).le.trans
      (Submodule.smul_mono le_rfl le_top)
  exact hmap (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

/-- An ideal annihilating the original section module also annihilates
its actual twist on every open subordinate to the chosen frame. -/
theorem IsFrameOn.smul_top_tensor_eq_bot (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) (J : Ideal Γ(X, W))
    (hzero : J • (⊤ : Submodule Γ(X, W) Γ(M, W)) = ⊥) :
    J • (⊤ : Submodule Γ(X, W) Γ(M ⊗ L, W)) = ⊥ := by
  let t : Γ(L, W) := L.presheaf.map (homOfLE hWU).op s
  let l : Γ(M, W) →ₗ[Γ(X, W)] Γ(M ⊗ L, W) := tensorFrameMap M t
  have hl : Function.Surjective l := (hs.bijective_tensorSections M hWU hWV).2
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro a ha y _hy
  obtain ⟨x, rfl⟩ := hl y
  have hx : a • x = 0 := by
    apply (Submodule.mem_bot Γ(X, W)).mp
    rw [← hzero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  apply (Submodule.mem_bot Γ(X, W)).mpr
  exact (l.map_smul a x).symm.trans ((congrArg l hx).trans l.map_zero)

/-- On an actual frame cover, a morphism whose composite with the
twisted nilpotent quotient is epimorphic is itself epimorphic.
The hypotheses refer only to the original untwisted affine sections. -/
theorem Hom.epi_of_tensor_nilpotent_quotient {P : X.Modules}
    [P.IsQuasicoherent] [(tensor N L).IsQuasicoherent]
    (q : M ⟶ N) (ψ : P ⟶ M ⊗ L) [Epi (ψ ≫ (q ▷ L))]
    {ι : Type u} (C : ι → X.Opens) (t : ∀ i : ι, Γ(L, C i))
    (hframe : ∀ i : ι, IsFrameOn (t i) (C i)) (hcover : ⨆ i : ι, C i = ⊤)
    (J : (W : X.Opens) → Ideal Γ(X, W)) (e : ℕ)
    (hker : ∀ (W : X.Opens), IsAffineOpen W →
      ((q.val.app (op W)).hom).ker ≤ J W • (⊤ : Submodule Γ(X, W) Γ(M, W)))
    (hpow : ∀ (W : X.Opens), IsAffineOpen W →
      (J W) ^ e • (⊤ : Submodule Γ(X, W) Γ(M, W)) = ⊥) : Epi ψ := by
  apply (Hom.epi_iff_locallySurjective ψ).mpr
  intro V z x hx
  have hxC : x ∈ ⨆ i : ι, C i := by
    rw [hcover]
    exact Set.mem_univ x
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxC
  obtain ⟨W, hW, hxW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ V ⊓ C i from ⟨hx, hxi⟩)
  have hWC : W ≤ C i := hWV.trans inf_le_right
  have hWV' : W ≤ V := hWV.trans inf_le_left
  let ψW : Γ(P, W) →ₗ[Γ(X, W)] Γ(M ⊗ L, W) := (ψ.val.app (op W)).hom
  let qW : Γ(M ⊗ L, W) →ₗ[Γ(X, W)] Γ(N ⊗ L, W) :=
    ((q ▷ L).val.app (op W)).hom
  have hcomp : Function.Surjective (qW.comp ψW) :=
    Hom.app_surjective_of_epi_of_isAffineOpen (ψ ≫ (q ▷ L)) W hW
  have hsurj : Function.Surjective ψW :=
    LinearMap.surjective_of_comp_surjective_of_ker_le_smul_of_pow_smul_eq_bot
      ψW qW (J W) e hcomp
      ((hframe i).whiskerRight_app_ker_le_smul hWC hWC q (J W) (hker W hW))
      ((hframe i).smul_top_tensor_eq_bot hWC hWC ((J W) ^ e) (hpow W hW))
  obtain ⟨y, hy⟩ := hsurj ((M ⊗ L).presheaf.map (homOfLE hWV').op z)
  exact ⟨W, hWV', hxW, y, hy⟩

end AlgebraicGeometry.Scheme.Modules
