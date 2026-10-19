/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorWithFrame
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Topology.Sets.Opens

/-!
# Exactness of tensoring with an actual frame cover

On an open admitting a frame, the actual tensor section map is a
bijection. This detects the injectivity of a tensored morphism locally;
separatedness then proves injectivity on every open. The existing
right adjoint to the tensor functor supplies right exactness, so this
local computation proves that tensoring preserves short exact sequences.

The frame data are actual sections with their original restrictions.
Neither exactness nor a comparison isomorphism is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem app_restriction {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) {U V : X.Opens} (hVU : V ≤ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE hVU).op m) =
      N.presheaf.map (homOfLE hVU).op (φ.app U m) :=
  congrArg (fun a : Γ(M, U) ⟶ Γ(N, V) => a.hom m)
    (φ.mapPresheaf.naturality (homOfLE hVU).op)

variable {X : Scheme.{u}} (L : X.Modules) {ι : Type u}
  (U : ι → X.Opens) (s : ∀ i : ι, Γ(L, U i))
  (hs : ∀ i : ι, IsFrameOn (s i) (U i)) (hcover : ⨆ i : ι, U i = ⊤)

include U s hs hcover

/-- A genuine cover by local frames makes tensoring preserve every
monomorphism of module sheaves, without assumptions on its source. -/
theorem mono_whiskerRight_of_frame_cover {M N : X.Modules}
    (φ : M ⟶ N) [Mono φ] : Mono (φ ▷ L) := by
  apply (Hom.mono_iff_injective (φ ▷ L)).mpr
  intro W x y hxy
  let W' : ι → X.Opens := fun i => W ⊓ U i
  have hW'W : ∀ i : ι, W' i ≤ W := fun _ => inf_le_left
  have hW' : W ≤ ⨆ i : ι, W' i := by
    intro p hp
    have hpU : p ∈ ⨆ i : ι, U i := by
      rw [hcover]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hpU
    exact Opens.mem_iSup.mpr ⟨i, hp, hi⟩
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    (M ⊗ L) W' W hW'W hW').1
  intro i
  let t : Γ(L, W' i) := L.presheaf.map (homOfLE (inf_le_right : W' i ≤ U i)).op (s i)
  obtain ⟨a, ha⟩ := ((hs i).bijective_tensorSections M
    (inf_le_right : W' i ≤ U i) inf_le_right).2
      ((M ⊗ L).presheaf.map (homOfLE (hW'W i)).op x)
  obtain ⟨b, hb⟩ := ((hs i).bijective_tensorSections M
    (inf_le_right : W' i ≤ U i) inf_le_right).2
      ((M ⊗ L).presheaf.map (homOfLE (hW'W i)).op y)
  have heq : (φ ▷ L).app (W' i)
        ((M ⊗ L).presheaf.map (homOfLE (hW'W i)).op x) =
      (φ ▷ L).app (W' i)
        ((M ⊗ L).presheaf.map (homOfLE (hW'W i)).op y) := by
    calc
      _ = (N ⊗ L).presheaf.map (homOfLE (hW'W i)).op ((φ ▷ L).app W x) :=
        app_restriction (φ ▷ L) (hW'W i) x
      _ = (N ⊗ L).presheaf.map (homOfLE (hW'W i)).op ((φ ▷ L).app W y) :=
        congrArg ((N ⊗ L).presheaf.map (homOfLE (hW'W i)).op) hxy
      _ = _ := (app_restriction (φ ▷ L) (hW'W i) y).symm
  rw [← ha, ← hb, whiskerRight_app_tensorSections, whiskerRight_app_tensorSections] at heq
  have hab : a = b :=
    ((Hom.mono_iff_injective φ).mp inferInstance (W' i))
      ((hs i).injective_tensorSections N
        (inf_le_right : W' i ≤ U i) inf_le_right heq)
  exact ha.symm.trans ((congrArg (fun m : Γ(M, W' i) => tensorSections m t) hab).trans hb)

/-- Tensoring by a sheaf with an actual frame cover preserves finite
limits. Right exactness comes from the existing tensor adjunction. -/
theorem tensorRight_preservesFiniteLimits_of_frame_cover :
    PreservesFiniteLimits (tensorRight L) := by
  have : (tensorRight L).IsLeftAdjoint := inferInstance
  have hcolim : PreservesFiniteColimits (tensorRight L) := inferInstance
  have : (tensorRight L).Additive :=
    rightExactFunctor_le_additiveFunctor X.Modules X.Modules (tensorRight L) hcolim
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (tensorRight L)).mpr
  intro S hS
  have : Mono S.f := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (tensorRight L)).mp hcolim S hS).1,
    mono_whiskerRight_of_frame_cover L U s hs hcover S.f⟩

/-- The original tensor functor maps every short exact sequence to an
actual short exact sequence when its second factor has a frame cover. -/
theorem shortExact_tensorRight_of_frame_cover (S : ShortComplex X.Modules)
    (hS : S.ShortExact) : (S.map (tensorRight L)).ShortExact := by
  have : (tensorRight L).IsLeftAdjoint := inferInstance
  have : PreservesFiniteLimits (tensorRight L) :=
    tensorRight_preservesFiniteLimits_of_frame_cover L U s hs hcover
  exact hS.map_of_exact (tensorRight L)

end AlgebraicGeometry.Scheme.Modules
