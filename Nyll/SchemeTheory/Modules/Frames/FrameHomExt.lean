/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sets.Opens

/-!
# Morphisms determined by original frames on a cover

A morphism of native module sheaves is determined by its values on global
sections which give local frames on a covering family. On each smaller
open the frame expresses every source section as a scalar multiple of
the restricted global section. The actual restriction naturality and
sheaf separatedness then identify the original morphisms.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Equality on original global frames over a cover determines the
original native module-sheaf morphism on all sections. -/
theorem hom_ext_of_frame_cover {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type u} (U : ι → X.Opens) (s : ι → Γ(M, ⊤))
    (hframe : ∀ i : ι, IsFrameOn (s i) (U i)) (hcover : ⨆ i : ι, U i = ⊤)
    (φ ψ : M ⟶ N) (h : ∀ i : ι, φ.app ⊤ (s i) = ψ.app ⊤ (s i)) : φ = ψ := by
  apply hom_ext
  intro W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  let C : ι → X.Opens := fun i => W ⊓ U i
  have hCW : ∀ i : ι, C i ≤ W := fun _ => inf_le_left
  have hW : W ≤ ⨆ i : ι, C i := by
    intro z hz
    have hzU : z ∈ ⨆ i : ι, U i := by
      rw [hcover]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hzU
    exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible N C W hCW hW).1
  intro i
  let t : Γ(M, C i) := M.presheaf.map (homOfLE (le_top : C i ≤ ⊤)).op (s i)
  let y : Γ(M, C i) := M.presheaf.map (homOfLE (hCW i)).op x
  obtain ⟨r, hr⟩ := ((hframe i).bijective (le_top : C i ≤ ⊤) inf_le_right).2 y
  have hφ : φ.app (C i) t =
      N.presheaf.map (homOfLE (le_top : C i ≤ ⊤)).op (φ.app ⊤ (s i)) :=
    PresheafOfModules.naturality_apply φ.val (homOfLE (le_top : C i ≤ ⊤)).op (s i)
  have hψ : ψ.app (C i) t =
      N.presheaf.map (homOfLE (le_top : C i ≤ ⊤)).op (ψ.app ⊤ (s i)) :=
    PresheafOfModules.naturality_apply ψ.val (homOfLE (le_top : C i ≤ ⊤)).op (s i)
  have ht : φ.app (C i) t = ψ.app (C i) t :=
    hφ.trans ((congrArg (N.presheaf.map (homOfLE (le_top : C i ≤ ⊤)).op)
      (h i)).trans hψ.symm)
  have hy : φ.app (C i) y = ψ.app (C i) y := by
    calc
      φ.app (C i) y = φ.app (C i) (r • t) := congrArg (φ.app (C i)) hr.symm
      _ = r • φ.app (C i) t := φ.app_smul r t
      _ = r • ψ.app (C i) t :=
        congrArg (fun z : Γ(N, C i) => r • z) ht
      _ = ψ.app (C i) (r • t) := (ψ.app_smul r t).symm
      _ = ψ.app (C i) y := congrArg (ψ.app (C i)) hr
  exact (PresheafOfModules.naturality_apply φ.val (homOfLE (hCW i)).op x).symm.trans
    (hy.trans (PresheafOfModules.naturality_apply ψ.val (homOfLE (hCW i)).op x))

end AlgebraicGeometry.Scheme.Modules
