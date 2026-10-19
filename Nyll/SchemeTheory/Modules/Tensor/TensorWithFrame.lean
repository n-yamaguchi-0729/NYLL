/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic.Choose

/-!
# Tensoring sections with a local frame

Tensoring an arbitrary module sheaf with a chosen local frame gives a
bijection on sections over every subordinate open. The presheaf tensor
comparison has actual local preimages and locally detects equality.
The frame identifies each such presheaf tensor with a unique section of
the first factor. These local sections agree and glue in that factor.

The first factor is arbitrary; quasicoherence or local freeness of that
factor is not needed.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameTensor

/-- Tensoring with a chosen basis of a rank-one module gives the actual
tensor-product linear equivalence on underlying elements. -/
theorem bijective_tmul_of_bijective_smul {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (t : N) (ht : Function.Bijective (fun r : R => r • t)) :
    Function.Bijective (fun m : M => m ⊗ₜ[R] t) := by
  let eN : R ≃ₗ[R] N := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R N t) ht
  let e : M ≃ₗ[R] M ⊗[R] N :=
    (TensorProduct.rid R M).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R M) eN)
  have he : (fun m : M => m ⊗ₜ[R] t) = e := by
    funext m
    change m ⊗ₜ[R] t =
      TensorProduct.congr (LinearEquiv.refl R M) eN ((TensorProduct.rid R M).symm m)
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_tmul]
    change m ⊗ₜ[R] t = m ⊗ₜ[R] ((1 : R) • t)
    rw [one_smul]
  rw [he]
  exact e.bijective

private abbrev res {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (hVU : V ≤ U) : Γ(M, U) →+ Γ(M, V) :=
  (M.presheaf.map (homOfLE hVU).op).hom

private theorem res_res {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(M, U)) :
    res M hWV (res M hVU s) = res M (hWV.trans hVU) s := by
  change (M.presheaf.map (homOfLE hVU).op ≫ M.presheaf.map (homOfLE hWV).op) s = _
  rw [← Functor.map_comp]
  rfl

private theorem res_tensor_frame {X : Scheme.{u}} {F L : X.Modules}
    {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (s : Γ(L, U)) (m : Γ(F, V)) :
    res (F ⊗ L) hWV (Modules.tensorSections m (res L hVU s)) =
      Modules.tensorSections (res F hWV m) (res L (hWV.trans hVU) s) :=
  (map_tensorSections (homOfLE hWV) m (res L hVU s)).trans
    (congrArg (Modules.tensorSections (res F hWV m)) (res_res L hVU hWV s))

variable {X : Scheme.{u}} (F : X.Modules) {L : X.Modules}
  {U V W : X.Opens} {s : Γ(L, U)}

/-- Every tensor section is locally a pure tensor with a specified frame
of its second factor. -/
theorem IsFrameOn.exists_local_tensor_preimage (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) (y : Γ(F ⊗ L, W)) {x : X} (hx : x ∈ W) :
    ∃ W' : X.Opens, ∃ hW'W : W' ≤ W, x ∈ W' ∧
      ∃ m : Γ(F, W'),
        Modules.tensorSections m (L.presheaf.map (homOfLE (hW'W.trans hWU)).op s) =
          (F ⊗ L).presheaf.map (homOfLE hW'W).op y := by
  obtain ⟨W', i, hxW', z, hz⟩ := exists_local_preimage (L := F) (M := L) y hx
  obtain ⟨m, hm⟩ := (bijective_tmul_of_bijective_smul
    (M := Γ(F, W')) (res L (i.le.trans hWU) s)
    (hs (i.le.trans hWU) (i.le.trans hWV))).2 z
  refine ⟨W', i.le, hxW', m, ?_⟩
  exact (congrArg (tsApp F L W') hm).trans hz

/-- Tensoring with a local frame is injective on actual section modules. -/
theorem IsFrameOn.injective_tensorSections (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Injective (fun m : Γ(F, W) =>
      Modules.tensorSections m (L.presheaf.map (homOfLE hWU).op s)) := by
  classical
  intro m m' hmm'
  have hlocal : ∀ x : W, ∃ W' : X.Opens, ∃ hW'W : W' ≤ W,
      x.val ∈ W' ∧ res F hW'W m = res F hW'W m' := by
    intro x
    let z : Γ(F, W) ⊗[Γ(X, W)] Γ(L, W) := m ⊗ₜ[Γ(X, W)] res L hWU s
    let z' : Γ(F, W) ⊗[Γ(X, W)] Γ(L, W) := m' ⊗ₜ[Γ(X, W)] res L hWU s
    have heq : tsApp F L W z = tsApp F L W z' := hmm'
    obtain ⟨W', i, hxW', hzz'⟩ := exists_local_eq (L := F) (M := L) z z' heq x.property
    dsimp only [z, z'] at hzz'
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
      PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul] at hzz'
    have hres : L.presheaf.map i.op (res L hWU s) =
        res L (i.le.trans hWU) s := res_res L hWU i.le s
    change (res F i.le m) ⊗ₜ[Γ(X, W')] (L.presheaf.map i.op (res L hWU s)) =
      (res F i.le m') ⊗ₜ[Γ(X, W')] (L.presheaf.map i.op (res L hWU s)) at hzz'
    rw [hres] at hzz'
    exact ⟨W', i.le, hxW', (bijective_tmul_of_bijective_smul
      (M := Γ(F, W')) (res L (i.le.trans hWU) s)
      (hs (i.le.trans hWU) (i.le.trans hWV))).1 hzz'⟩
  choose W' hW'W hxW' heq using hlocal
  have hcover : W ≤ ⨆ x : W, W' x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW' ⟨x, hx⟩⟩
  exact (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible F W' W hW'W hcover).1
    m m' heq

/-- The actual tensor product with a local frame gives a bijection on
sections over every subordinate open subset. -/
theorem IsFrameOn.bijective_tensorSections (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective (fun m : Γ(F, W) =>
      Modules.tensorSections m (L.presheaf.map (homOfLE hWU).op s)) := by
  classical
  refine ⟨hs.injective_tensorSections F hWU hWV, ?_⟩
  intro y
  have hlocal := fun x : W => hs.exists_local_tensor_preimage F hWU hWV y x.property
  choose W' hW'W hxW' m hm using hlocal
  have hcover : W ≤ ⨆ x : W, W' x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW' ⟨x, hx⟩⟩
  have hcompatible : ∀ x x' : W,
      res F (inf_le_left : W' x ⊓ W' x' ≤ W' x) (m x) =
        res F (inf_le_right : W' x ⊓ W' x' ≤ W' x') (m x') := by
    intro x x'
    apply hs.injective_tensorSections F
      ((inf_le_left.trans (hW'W x)).trans hWU)
      ((inf_le_left.trans (hW'W x)).trans hWV)
    calc
      Modules.tensorSections (res F (inf_le_left : W' x ⊓ W' x' ≤ W' x) (m x))
          (res L ((inf_le_left.trans (hW'W x)).trans hWU) s) =
        res (F ⊗ L) inf_le_left (res (F ⊗ L) (hW'W x) y) :=
          (res_tensor_frame ((hW'W x).trans hWU) inf_le_left s (m x)).symm.trans
            (congrArg (res (F ⊗ L) (V := W' x ⊓ W' x') inf_le_left) (hm x))
      _ = res (F ⊗ L) (inf_le_left.trans (hW'W x)) y :=
        res_res (F ⊗ L) (hW'W x) inf_le_left y
      _ = res (F ⊗ L) (inf_le_right.trans (hW'W x')) y := rfl
      _ = res (F ⊗ L) inf_le_right (res (F ⊗ L) (hW'W x') y) :=
        (res_res (F ⊗ L) (hW'W x') inf_le_right y).symm
      _ = Modules.tensorSections (res F (inf_le_right : W' x ⊓ W' x' ≤ W' x') (m x'))
          (res L ((inf_le_left.trans (hW'W x)).trans hWU) s) :=
        (congrArg (res (F ⊗ L) (V := W' x ⊓ W' x') inf_le_right) (hm x')).symm.trans
          (res_tensor_frame ((hW'W x').trans hWU) inf_le_right s (m x'))
  obtain ⟨a, ha⟩ :=
    (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible F W' W hW'W hcover).2
      m hcompatible
  refine ⟨a, ?_⟩
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible (F ⊗ L)
    W' W hW'W hcover).1
  intro x
  exact (res_tensor_frame hWU (hW'W x) s a).trans
    ((congrArg (fun b : Γ(F, W' x) =>
      Modules.tensorSections b (res L ((hW'W x).trans hWU) s)) (ha x)).trans (hm x))

end AlgebraicGeometry.Scheme.Modules
