/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.RingTheory.AdicCompletion.SequenceLimit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Actual sections of inverse limits of module sheaves

Evaluation of native module sheaves preserves limits. Combining that
fact with the explicit universal compatible-sequence cone identifies
sections of a countable inverse limit with the original compatible
sections. The comparison preserves each original projection and every
restriction to a smaller open.

No quasicoherence of the inverse limit is asserted or assumed. In an
adic application, its finite reductions and the associated graded layers
are compared with the original coherent stages separately.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- Evaluation retains the native module of sections and its scalar action. -/
def moduleSectionsFunctor (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  (sheafOfModulesEquivalence X).functor ⋙
    SheafOfModules.evaluation X.ringCatSheaf (op U)

instance moduleSectionsFunctor_preservesSequentialLimits (U : X.Opens) :
    PreservesLimitsOfShape ℕᵒᵖ (moduleSectionsFunctor U) :=
  inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
    ((sheafOfModulesEquivalence X).functor ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op U)))

variable (D : ℕᵒᵖ ⥤ X.Modules) (U : X.Opens)

/-- Sections of the native limit are the actual compatible section sequences. -/
def limitSectionsEquiv : Γ(limit D, U) ≃ₗ[Γ(X, U)]
    AdicModuleSystem.sections
      (fun n : ℕ => (moduleSectionsFunctor U).obj (D.obj (op n)))
      (fun n : ℕ => ((moduleSectionsFunctor U).map
        (D.map (homOfLE (Nat.le_add_right n 1)).op)).hom) := by
  let Q := moduleSectionsFunctor U
  let e₁ := (preservesLimitIso Q D).toLinearEquiv
  let e₂ := AdicModuleSystem.sequenceLimitEquiv (D ⋙ Q)
  let e := e₁.trans e₂
  exact e

/-- Each component is the actual section map of the original limit projection. -/
theorem limitSectionsEquiv_apply (x : Γ(limit D, U)) (n : ℕ) :
    (limitSectionsEquiv D U x).val n = ((limit.π D (op n)).val.app (op U)).hom x := by
  let Q := moduleSectionsFunctor U
  have h₁ := AdicModuleSystem.sequenceLimitEquiv_apply (D ⋙ Q)
    ((preservesLimitIso Q D).toLinearEquiv x) n
  have h₂ := congrArg
    (fun a : Q.obj (limit D) ⟶ Q.obj (D.obj (op n)) => a.hom x)
      (preservesLimitIso_hom_π Q D (op n))
  exact h₁.trans h₂

/-- The comparison commutes with the original restriction map on every open. -/
theorem limitSectionsEquiv_restriction {V : X.Opens} (h : V ≤ U)
    (x : Γ(limit D, U)) (n : ℕ) :
    (limitSectionsEquiv D V ((limit D).presheaf.map (homOfLE h).op x)).val n =
      (D.obj (op n)).presheaf.map (homOfLE h).op ((limitSectionsEquiv D U x).val n) := by
  rw [limitSectionsEquiv_apply, limitSectionsEquiv_apply]
  have hnat := (limit.π D (op n)).mapPresheaf.naturality (homOfLE h).op
  exact congrArg (fun a : Γ(limit D, U) ⟶ Γ(D.obj (op n), V) => a.hom x) hnat

variable (M : ℕ → X.Modules) (t : ∀ n : ℕ, M (n + 1) ⟶ M n)

/-- For an original sequence of sheaf morphisms, the compatibility equations
are the original successor section maps themselves. -/
def sequenceSectionsEquiv : Γ(limit (Functor.ofOpSequence t), U) ≃ₗ[Γ(X, U)]
    AdicModuleSystem.sections (R := Γ(X, U))
      (fun n : ℕ => (moduleSectionsFunctor U).obj (M n))
      (fun n : ℕ => ((moduleSectionsFunctor U).map (t n)).hom) := by
  let D' : ℕᵒᵖ ⥤ X.Modules := Functor.ofOpSequence t
  let Q := moduleSectionsFunctor U
  have h : (fun n : ℕ => (Q.map (D'.map (homOfLE (Nat.le_add_right n 1)).op)).hom) =
      (fun n : ℕ => (Q.map (t n)).hom) := by
    funext n
    rw [show D'.map (homOfLE (Nat.le_add_right n 1)).op = t n from
      Functor.ofOpSequence_map_homOfLE_succ t n]
    rfl
  let e₁ := limitSectionsEquiv D' U
  let e₂ := LinearEquiv.ofEq _ _
    (congrArg (AdicModuleSystem.sections (R := Γ(X, U))
      (fun n : ℕ => Q.obj (M n))) h)
  exact e₁.trans e₂

/-- The sequence comparison is induced by the original native limit projection. -/
theorem sequenceSectionsEquiv_apply (x : Γ(limit (Functor.ofOpSequence t), U)) (n : ℕ) :
    (sequenceSectionsEquiv (U := U) M t x).val n =
      ((limit.π (Functor.ofOpSequence t) (op n)).val.app (op U)).hom x :=
  limitSectionsEquiv_apply (Functor.ofOpSequence t) U x n

/-- Every restriction retains the literal original component of a compatible sequence. -/
theorem sequenceSectionsEquiv_restriction {V : X.Opens} (h : V ≤ U)
    (x : Γ(limit (Functor.ofOpSequence t), U)) (n : ℕ) :
    (sequenceSectionsEquiv (U := V) M t
      ((limit (Functor.ofOpSequence t)).presheaf.map (homOfLE h).op x)).val n =
      (M n).presheaf.map (homOfLE h).op ((sequenceSectionsEquiv (U := U) M t x).val n) :=
  limitSectionsEquiv_restriction (Functor.ofOpSequence t) U h x n

end AlgebraicGeometry.Scheme.Modules
