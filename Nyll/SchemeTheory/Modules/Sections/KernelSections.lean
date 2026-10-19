/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Submodules.KernelSubmoduleScheme
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Actual sections of a kernel sheaf

The constructed sectionwise kernel subsheaf is the native categorical
kernel. Evaluate that actual isomorphism to identify sections on any
open with the kernel of the original section map. The inclusion is the
original categorical kernel inclusion, and its naturality gives the
original restriction of every kernel section.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)

/-- Sections of the original kernel sheaf are the kernel of the
original section map, with the native section-ring action. -/
def kernelSectionsEquiv (U : X.Opens) :
    (moduleSectionsFunctor U).obj (kernel φ) ≃ₗ[Γ(X, U)]
      ↥(((moduleSectionsFunctor U).map φ).hom.ker) := by
  let e := (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso
    (kernelSubmoduleIso φ).symm
  exact e.toLinearEquiv

/-- The comparison is precisely the actual kernel inclusion on sections. -/
theorem kernelSectionsEquiv_apply (U : X.Opens)
    (x : (moduleSectionsFunctor U).obj (kernel φ)) :
    (kernelSectionsEquiv φ U x).val = (kernel.ι φ).app U x := by
  let E := sheafOfModulesEquivalence X
  let e := kernelSubmoduleIso φ
  have h : e.inv ≫ (kernelSubmodule φ).ι = E.functor.map (kernel.ι φ) :=
    (Iso.inv_comp_eq e).mpr (kernelSubmoduleIso_hom_ι φ).symm
  have hx := congrArg
    (fun k : E.functor.obj (kernel φ) ⟶ E.functor.obj M => (k.val.app (op U)).hom x) h
  exact hx

/-- The inverse comparison keeps the actual element of the original
section-map kernel. -/
theorem kernelSectionsEquiv_symm_apply (U : X.Opens)
    (x : ↥(((moduleSectionsFunctor U).map φ).hom.ker)) :
    (kernel.ι φ).app U ((kernelSectionsEquiv φ U).symm x) = x.val := by
  have h := kernelSectionsEquiv_apply φ U ((kernelSectionsEquiv φ U).symm x)
  exact h.symm.trans
    (congrArg Subtype.val ((kernelSectionsEquiv φ U).apply_symm_apply x))

/-- The kernel-section equivalence retains the original restriction
in the ambient module sheaf on every smaller open. -/
theorem kernelSectionsEquiv_restriction {U V : X.Opens} (h : V ≤ U)
    (x : (moduleSectionsFunctor U).obj (kernel φ)) :
    (kernelSectionsEquiv φ V ((kernel φ).presheaf.map (homOfLE h).op x)).val =
      M.presheaf.map (homOfLE h).op (kernelSectionsEquiv φ U x).val := by
  let y : Γ(kernel φ, U) := x
  have hnat := congrArg (fun k : Γ(kernel φ, U) ⟶ Γ(M, V) => k y)
    ((kernel.ι φ).mapPresheaf.naturality (homOfLE h).op)
  have hv := kernelSectionsEquiv_apply φ V
    ((kernel φ).presheaf.map (homOfLE h).op x)
  have hu := kernelSectionsEquiv_apply φ U x
  exact hv.trans (hnat.trans
    (congrArg (fun z : Γ(M, U) => M.presheaf.map (homOfLE h).op z) hu.symm))

end AlgebraicGeometry.Scheme.Modules
