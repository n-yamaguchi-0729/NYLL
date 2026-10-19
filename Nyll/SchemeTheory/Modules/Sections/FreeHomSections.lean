/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Submodules.FiniteSectionSubmodule
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Logic.Equiv.Basic

/-!
# Morphisms from a free sheaf and original global sections

Evaluation at the top open identifies a compatible section family
with its original global section. Applying this to the universal
property of the actual free sheaf gives a bijection between native
scheme-module morphisms and families of original global sections.

The comparison evaluates a morphism on the original free generators.
Its inverse and composition formulas retain those original maps; no
quasicoherence or finiteness condition is imposed.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- A compatible family is exactly its original section on the top open. -/
def sectionsTopEquiv : M.sections ≃ Γ(M, ⊤) where
  toFun s := s.val (op ⊤)
  invFun s := M.topSection s
  left_inv s := PresheafOfModules.sections_ext _ _
    (fun U => PresheafOfModules.sections_property s U.unop.leTop.op)
  right_inv s := SheafOfModules.topSection_top M s

/-- Evaluation in the top-section comparison is the original evaluation. -/
theorem sectionsTopEquiv_apply (s : M.sections) :
    sectionsTopEquiv M s = s.val (op ⊤) := rfl

/-- The inverse top-section comparison restricts the original section. -/
theorem sectionsTopEquiv_symm_apply (s : Γ(M, ⊤)) (U : X.Opens) :
    ((sectionsTopEquiv M).symm s).val (op U) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := rfl

/-- Morphisms from the actual free sheaf correspond to families of
original global sections, in the native scheme-module category. -/
def freeHomTopSectionsEquiv (I : Type u) :
    ((show X.Modules from SheafOfModules.free I) ⟶ M) ≃ (I → Γ(M, ⊤)) := by
  let e : ((show X.Modules from SheafOfModules.free I) ⟶ M) ≃
      ((SheafOfModules.free (R := X.ringCatSheaf) I) ⟶
        (show SheafOfModules.{u} X.ringCatSheaf from M)) :=
    (sheafOfModulesEquivalence X).fullyFaithfulFunctor.homEquiv
  exact e.trans ((SheafOfModules.freeHomEquiv M).trans
    (Equiv.piCongrRight (fun _ : I => sectionsTopEquiv M)))

/-- The forward comparison applies the original morphism to the
original free generator on the top open. -/
theorem freeHomTopSectionsEquiv_apply (I : Type u)
    (φ : (show X.Modules from SheafOfModules.free I) ⟶ M) (i : I) :
    freeHomTopSectionsEquiv M I φ i =
      φ.app ⊤ ((SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op ⊤)) := rfl

/-- The inverse comparison sends each original free generator to
the prescribed global section. -/
theorem freeHomTopSectionsEquiv_symm_generator (I : Type u)
    (s : I → Γ(M, ⊤)) (i : I) :
    ((freeHomTopSectionsEquiv M I).symm s).app ⊤
        ((SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op ⊤)) = s i :=
  congrFun ((freeHomTopSectionsEquiv M I).apply_symm_apply s) i

/-- Composition acts on the original global-section family by the
original section map of the second morphism. -/
theorem freeHomTopSectionsEquiv_comp {N : X.Modules} (I : Type u)
    (φ : (show X.Modules from SheafOfModules.free I) ⟶ M) (ψ : M ⟶ N) (i : I) :
    freeHomTopSectionsEquiv N I (φ ≫ ψ) i =
      ψ.app ⊤ (freeHomTopSectionsEquiv M I φ i) := rfl

end AlgebraicGeometry.Scheme.Modules
