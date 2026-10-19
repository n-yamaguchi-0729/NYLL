/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModulePresentationFiniteH
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Vanishing through a graded presentation

If the free source has zero cohomology in degree `i+1` and the actual
presentation kernel has zero cohomology in degree `i+2`, the presented
module has zero cohomology in degree `i+1`. The proof uses the previously
constructed connecting cocycle and then exhibits a boundary in the
original Čech complex. This is the dimension-shifting step of Serre
vanishing for finitely generated graded modules.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

open AlgebraicCurves.Cohomology.Cech.Proofs
open ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.ProjSpaceCech.GradedModule

/-- Vanishing of the two adjacent groups in the actual presentation
complex makes every cocycle of the presented module a boundary. -/
theorem Presentation.subsingleton_H_succ_of_subsingleton
    {R : Type u} [CommRing R] {n : ℕ} {D : GradedModule R n}
    (σ : Presentation D) (i : ℕ)
    (hF : Subsingleton (H σ.F (i + 1)))
    (hK : Subsingleton (H σ.ker (i + 1 + 1))) :
    Subsingleton (H D (i + 1)) := by
  change Subsingleton ((LinearMap.ker (GradedModule.d D (i + 1))) ⧸
    (LinearMap.range (GradedModule.d D i)).comap
      (LinearMap.ker (GradedModule.d D (i + 1))).subtype)
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro z
  have hδ : delta0 σ (i + 1) z = 0 := hK.elim _ _
  obtain ⟨f, hf⟩ := ker_delta0_le σ (i + 1) (LinearMap.mem_ker.mpr hδ)
  have hboundary : f.val ∈ LinearMap.range (GradedModule.d σ.F i) :=
    (Submodule.Quotient.mk_eq_zero
      ((LinearMap.range (GradedModule.d σ.F i)).comap
        (LinearMap.ker (GradedModule.d σ.F (i + 1))).subtype)).mp
      (hF.elim (Submodule.Quotient.mk f : H σ.F (i + 1)) 0)
  obtain ⟨w, hw⟩ := hboundary
  change z.val ∈ LinearMap.range (GradedModule.d D i)
  refine ⟨Hom.cochainMap σ.hom i w, ?_⟩
  calc
    GradedModule.d D i (Hom.cochainMap σ.hom i w) =
        Hom.cochainMap σ.hom (i + 1) (GradedModule.d σ.F i w) :=
      LinearMap.congr_fun (Hom.cochainMap_comm σ.hom i) w
    _ = Hom.cochainMap σ.hom (i + 1) f.val :=
      congrArg (Hom.cochainMap σ.hom (i + 1)) hw
    _ = z.val := congrArg Subtype.val hf

end ProjSpaceCech.GradedModule
