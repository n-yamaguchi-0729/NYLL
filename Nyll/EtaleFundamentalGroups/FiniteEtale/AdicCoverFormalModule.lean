/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineCompletion
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-!
# The actual inverse-limit module sheaf of the lifted covers

The native limit of the original direct-image module sheaves is constructed
on the fixed scheme. Its sections over an affine open identify with the
finite module over the completed affine coordinate ring already constructed
from the same cover tower. This identification preserves the original
projection maps.

For a locally Noetherian scheme every projection is surjective on affine
sections, its kernel is the actual power of the original section ideal,
and its quotient is the original stage module. Local surjectivity then
gives an epimorphism of the native module sheaves. These statements do not
assume or assert quasicoherence of the inverse-limit sheaf on the original
scheme; its algebraization is a further existence problem.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The actual native inverse-limit module sheaf of the original cover tower. -/
def formalModuleSheaf : X.Modules :=
  limit (Functor.ofOpSequence (moduleTransition f I V))

/-- The original native projection to a stage of the lifted cover tower. -/
def formalModuleProjection (n : ℕ) : formalModuleSheaf f I V ⟶ moduleSheaf f I V n :=
  limit.π (Functor.ofOpSequence (moduleTransition f I V)) (op n)

/-- Consecutive projections are compatible with the actual cover morphisms. -/
theorem formalModuleProjection_transition (n : ℕ) :
    formalModuleProjection f I V (n + 1) ≫ moduleTransition f I V n =
      formalModuleProjection f I V n := by
  have h := limit.w (Functor.ofOpSequence (moduleTransition f I V))
    (homOfLE (Nat.le_add_right n 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h

/-- The original affine section object with its native coordinate-ring action retained. -/
def formalAffineSectionModule (U : X.affineOpens) : ModuleCat Γ(X, U) :=
  (Scheme.Modules.moduleSectionsFunctor (U : X.Opens)).obj (formalModuleSheaf f I V)

/-- The original section projection with both native module objects fixed. -/
def formalAffineProjection (U : X.affineOpens) (n : ℕ) :
    formalAffineSectionModule f I V U →ₗ[Γ(X, U)] affineSectionModule f I V U n := by
  let p := (Scheme.Modules.moduleSectionsFunctor (U : X.Opens)).map
    (formalModuleProjection f I V n)
  exact p.hom

/-- Actual affine sections of the native limit identify with the constructed
module over the completed original coefficient ring. -/
def formalAffineCompletionEquiv (U : X.affineOpens) :
    formalAffineSectionModule f I V U ≃ₗ[Γ(X, U)]
      completedAffineSections f I V U := by
  let e₁ := Scheme.Modules.sequenceSectionsEquiv (U := (U : X.Opens))
    (moduleSheaf f I V) (moduleTransition f I V)
  let e₂ := affineSectionsCompletionEquiv f I V U
  exact e₁.trans e₂

/-- The comparison uses precisely the actual sheaf projection at every level. -/
theorem formalAffineCompletionEquiv_eval (U : X.affineOpens)
    (x : formalAffineSectionModule f I V U) (n : ℕ) :
    completedAffineSectionsEval f I V U n (formalAffineCompletionEquiv f I V U x) =
      formalAffineProjection f I V U n x := by
  have h₁ := completedAffineSectionsEval_completion f I V U n
    (Scheme.Modules.sequenceSectionsEquiv (U := (U : X.Opens))
      (moduleSheaf f I V) (moduleTransition f I V) x)
  have h₂ := Scheme.Modules.sequenceSectionsEquiv_apply (U := (U : X.Opens))
    (moduleSheaf f I V) (moduleTransition f I V) x n
  exact h₁.trans h₂

variable [IsLocallyNoetherian X]

/-- Every actual stage section on an affine open lifts to the native limit sheaf. -/
theorem formalModuleProjection_app_surjective (U : X.affineOpens) (n : ℕ) :
    Function.Surjective (formalAffineProjection f I V U n) := by
  intro y
  obtain ⟨z, hz⟩ := completedAffineSectionsEval_surjective f I V U n y
  let e := formalAffineCompletionEquiv f I V U
  refine ⟨e.symm z, ?_⟩
  rw [← formalAffineCompletionEquiv_eval, e.apply_symm_apply]
  exact hz

/-- The actual affine projection kernel is computed in the original
native section module, with its original coordinate-ring action. -/
theorem formalModuleProjection_app_ker (U : X.affineOpens) (n : ℕ) :
    (formalAffineProjection f I V U n).ker =
      (sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U)) := by
  let e := formalAffineCompletionEquiv f I V U
  have hker :
      (formalAffineProjection f I V U n).ker =
        ((completedAffineSectionsPower f I V U n).restrictScalars Γ(X, U)).comap
          e.toLinearMap := by
    ext x
    rw [← completedAffineSectionsEval_ker f I V U n]
    change _ = 0 ↔ completedAffineSectionsEval f I V U n (e x) = 0
    rw [formalAffineCompletionEquiv_eval]
  have hpower :
      (completedAffineSectionsPower f I V U n).restrictScalars Γ(X, U) =
        (sectionsIdeal f I U) ^ (n + 1) •
          (⊤ : Submodule Γ(X, U) (completedAffineSections f I V U)) := by
    rw [completedAffineSectionsPower, ← Ideal.map_pow,
      Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  have hrange : (⊤ : Submodule Γ(X, U) (completedAffineSections f I V U)) ≤
      LinearMap.range e.toLinearMap := by
    rw [LinearMap.range_eq_top.mpr e.surjective]
  rw [hker, hpower, Submodule.comap_smul'' e.injective hrange, Submodule.comap_top]

/-- The quotient of the native affine section module by the actual ideal power
recovers the original finite stage. -/
def formalAffineReductionEquiv (U : X.affineOpens) (n : ℕ) :
    ((formalAffineSectionModule f I V U) ⧸
      ((sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U))))
      ≃ₗ[Γ(X, U)] affineSectionModule f I V U n := by
  let p := formalAffineProjection f I V U n
  let e₁ := Submodule.quotEquivOfEq (R := Γ(X, U))
    (M := formalAffineSectionModule f I V U)
    ((sectionsIdeal f I U) ^ (n + 1) • ⊤) p.ker
    (formalModuleProjection_app_ker f I V U n).symm
  let e₂ := LinearMap.quotKerEquivOfSurjective (R := Γ(X, U))
    (M := formalAffineSectionModule f I V U)
    (M₂ := affineSectionModule f I V U n) p
    (formalModuleProjection_app_surjective f I V U n)
  exact e₁.trans e₂

/-- Reduction sends a representative to its original stage projection. -/
theorem formalAffineReductionEquiv_mk (U : X.affineOpens) (n : ℕ)
    (x : formalAffineSectionModule f I V U) :
    formalAffineReductionEquiv f I V U n (Submodule.Quotient.mk x) =
      formalAffineProjection f I V U n x := by
  have h := LinearMap.quotKerEquivOfSurjective_apply_mk (R := Γ(X, U))
    (M := formalAffineSectionModule f I V U)
    (M₂ := affineSectionModule f I V U n)
    (f := formalAffineProjection f I V U n)
    (formalModuleProjection_app_surjective f I V U n) x
  exact h

/-- The projections from the actual inverse-limit sheaf are epimorphisms,
by the proved affine section lifting property. -/
theorem formalModuleProjection_epi (n : ℕ) : Epi (formalModuleProjection f I V n) := by
  apply (Scheme.Modules.Hom.epi_iff_locallySurjective (formalModuleProjection f I V n)).mpr
  intro U s x hx
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨W, hWU, hxW, ?_⟩
  obtain ⟨z, hz⟩ := formalModuleProjection_app_surjective f I V ⟨W, hW⟩ n
    ((moduleSheaf f I V n).presheaf.map (homOfLE hWU).op s)
  exact ⟨z, hz⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
