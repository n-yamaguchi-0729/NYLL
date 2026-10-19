/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemOverCompletion
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Effective modules of actual affine sections of the lifted cover tower

On each affine open of the original scheme, take the original section
modules and their actual cover-induced transitions. Their compatible
sequences agree with the compatible sequences of the completed stages.
The latter form a finite module over the completed affine coefficient
ring when the scheme is locally Noetherian.

Every quotient of this constructed module recovers the original section
module, with its original evaluation and transition. Finiteness,
surjectivity, the adic kernels, and stage annihilation are supplied by the
actual finite cover tower. No completeness of the original affine ring
or effective module is supplied as an assumption.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The original native section object, retained together with its coefficient action. -/
def affineSectionModule (U : X.affineOpens) (n : ℕ) : ModuleCat Γ(X, U) :=
  (moduleSheaf f I V n).val.obj (op (U : X.Opens))

/-- The original native transition, using those same section objects. -/
def affineSectionTransition (U : X.affineOpens) (n : ℕ) :
    affineSectionModule f I V U (n + 1) →ₗ[Γ(X, U)] affineSectionModule f I V U n := by
  let t : affineSectionModule f I V U (n + 1) ⟶ affineSectionModule f I V U n :=
    (moduleTransition f I V n).val.app (op (U : X.Opens))
  exact t.hom

/-- Compatible sequences of the original native sections over an affine open. -/
def affineSections (U : X.affineOpens) :
    Submodule Γ(X, U) ((n : ℕ) → (affineSectionModule f I V U n)) :=
  AdicModuleSystem.sections (fun n => (affineSectionModule f I V U n))
    (fun n => affineSectionTransition f I V U n)

/-- The constructed module over the completed original affine coefficient ring. -/
def completedAffineSections (U : X.affineOpens) :
    Submodule (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      ((n : ℕ) → AdicCompletion (sectionsIdeal f I U) (affineSectionModule f I V U n)) :=
  AdicModuleSystem.sections
    (fun n => AdicCompletion (sectionsIdeal f I U) (affineSectionModule f I V U n))
    (fun n => AdicCompletion.map (sectionsIdeal f I U)
      (affineSectionTransition f I V U n))

/-- Completing the nilpotent stages preserves their original compatible sections. -/
def affineSectionsCompletionEquiv (U : X.affineOpens) :
    affineSections f I V U ≃ₗ[Γ(X, U)] completedAffineSections f I V U := by
  let e := AdicModuleSystem.completedSectionsEquiv (fun n => (affineSectionModule f I V U n))
    (fun n => affineSectionTransition f I V U n)
    (sectionsIdeal f I U) (fun n => moduleSheaf_sections_annihilated f I V n U)
  exact e

/-- The comparison keeps the literal completion of each original section. -/
theorem affineSectionsCompletionEquiv_apply (U : X.affineOpens)
    (x : affineSections f I V U) (n : ℕ) :
    (affineSectionsCompletionEquiv f I V U x).val n =
      AdicCompletion.of (sectionsIdeal f I U) (affineSectionModule f I V U n) (x.val n) :=
  AdicModuleSystem.completedSectionsEquiv_apply
    (fun k => (affineSectionModule f I V U k))
    (fun k => affineSectionTransition f I V U k)
    (sectionsIdeal f I U) (fun k => moduleSheaf_sections_annihilated f I V k U) x n

/-- Evaluation in the original, uncompleted native section module. -/
def completedAffineSectionsEval (U : X.affineOpens) (n : ℕ) :
    completedAffineSections f I V U →ₗ[Γ(X, U)] (affineSectionModule f I V U n) :=
  (AdicModuleSystem.eval (fun k => (affineSectionModule f I V U k))
    (fun k => affineSectionTransition f I V U k) n).comp
      (affineSectionsCompletionEquiv f I V U).symm.toLinearMap

/-- The original section is unchanged by completion and subsequent evaluation. -/
theorem completedAffineSectionsEval_completion (U : X.affineOpens) (n : ℕ)
    (x : affineSections f I V U) :
    completedAffineSectionsEval f I V U n (affineSectionsCompletionEquiv f I V U x) =
      x.val n :=
  congrArg (fun y : affineSections f I V U => y.val n)
    ((affineSectionsCompletionEquiv f I V U).symm_apply_apply x)

/-- The evaluations commute with the actual original cover transition. -/
theorem moduleTransition_completedAffineSectionsEval (U : X.affineOpens) (n : ℕ)
    (x : completedAffineSections f I V U) :
    affineSectionTransition f I V U n
        (completedAffineSectionsEval f I V U (n + 1) x) =
      completedAffineSectionsEval f I V U n x :=
  ((affineSectionsCompletionEquiv f I V U).symm x).property n

/-- The module constructed from the actual affine cover sections is finite
over the completed affine coefficient ring. -/
theorem completedAffineSections_finite [IsLocallyNoetherian X] (U : X.affineOpens) :
    Module.Finite (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineSections f I V U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have : ∀ n : ℕ, Module.Finite Γ(X, U) (affineSectionModule f I V U n) :=
    fun n => moduleSheaf_finite_sections f I V n U U.property
  have h := AdicModuleSystem.completed_sections_finite
    (fun n => (affineSectionModule f I V U n))
    (fun n => affineSectionTransition f I V U n)
    (sectionsIdeal f I U)
    (fun n => moduleSheaf_sections_annihilated f I V n U)
    (fun n => moduleTransition_app_surjective f I V n U U.property)
    (fun n => moduleTransition_app_ker f I V n U U.property)
  exact h

/-- The adic submodule in the actual completed affine module. -/
def completedAffineSectionsPower (U : X.affineOpens) (n : ℕ) :
    Submodule (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineSections f I V U) :=
  ((sectionsIdeal f I U).map
    (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^ (n + 1) • ⊤

/-- Reduction of the constructed affine module recovers the literal
original section module at the specified stage. -/
def completedAffineSectionsReductionEquiv [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) :
    ((completedAffineSections f I V U) ⧸ completedAffineSectionsPower f I V U n)
      ≃ₗ[Γ(X, U)] (affineSectionModule f I V U n) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have : ∀ k : ℕ, Module.Finite Γ(X, U) (affineSectionModule f I V U k) :=
    fun k => moduleSheaf_finite_sections f I V k U U.property
  let e := AdicModuleSystem.completedQuotientEquiv
    (fun k => (affineSectionModule f I V U k))
    (fun k => affineSectionTransition f I V U k)
    (sectionsIdeal f I U)
    (fun k => moduleSheaf_sections_annihilated f I V k U)
    (fun k => moduleTransition_app_surjective f I V k U U.property)
    (fun k => moduleTransition_app_ker f I V k U U.property) n
  exact e

/-- The reduction comparison is induced by evaluation of the original sections. -/
theorem completedAffineSectionsReductionEquiv_mk [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) (x : completedAffineSections f I V U) :
    completedAffineSectionsReductionEquiv f I V U n (Submodule.Quotient.mk x) =
      completedAffineSectionsEval f I V U n x := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have : ∀ k : ℕ, Module.Finite Γ(X, U) (affineSectionModule f I V U k) :=
    fun k => moduleSheaf_finite_sections f I V k U U.property
  exact AdicModuleSystem.completedQuotientEquiv_mk
    (fun k => (affineSectionModule f I V U k))
    (fun k => affineSectionTransition f I V U k)
    (sectionsIdeal f I U)
    (fun k => moduleSheaf_sections_annihilated f I V k U)
    (fun k => moduleTransition_app_surjective f I V k U U.property)
    (fun k => moduleTransition_app_ker f I V k U U.property) n x

/-- Every original affine section is the evaluation of a compatible sequence. -/
theorem completedAffineSectionsEval_surjective [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) :
    Function.Surjective (completedAffineSectionsEval f I V U n) := by
  intro x
  obtain ⟨y, hy⟩ := (completedAffineSectionsReductionEquiv f I V U n).surjective x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (completedAffineSectionsPower f I V U n) y
  exact ⟨z, (completedAffineSectionsReductionEquiv_mk f I V U n z).symm.trans hy⟩

/-- The original evaluation has precisely the expected completed adic kernel. -/
theorem completedAffineSectionsEval_ker [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) :
    (completedAffineSectionsEval f I V U n).ker =
      (completedAffineSectionsPower f I V U n).restrictScalars Γ(X, U) := by
  ext x
  change completedAffineSectionsEval f I V U n x = 0 ↔
    x ∈ completedAffineSectionsPower f I V U n
  constructor
  · intro hx
    apply (Submodule.Quotient.mk_eq_zero (completedAffineSectionsPower f I V U n)).mp
    apply (completedAffineSectionsReductionEquiv f I V U n).injective
    rw [map_zero, completedAffineSectionsReductionEquiv_mk]
    exact hx
  · intro hx
    rw [← completedAffineSectionsReductionEquiv_mk f I V U n x,
      (Submodule.Quotient.mk_eq_zero (completedAffineSectionsPower f I V U n)).mpr hx,
      map_zero]

/-- Consecutive reduction comparisons retain the actual cover transition. -/
theorem moduleTransition_completedAffineSectionsReductionEquiv [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) (x : completedAffineSections f I V U) :
    affineSectionTransition f I V U n
        (completedAffineSectionsReductionEquiv f I V U (n + 1)
          (Submodule.Quotient.mk x)) =
      completedAffineSectionsReductionEquiv f I V U n (Submodule.Quotient.mk x) := by
  rw [completedAffineSectionsReductionEquiv_mk, completedAffineSectionsReductionEquiv_mk]
  exact moduleTransition_completedAffineSectionsEval f I V U n x

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
