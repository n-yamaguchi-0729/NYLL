/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineCompletion
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineProjective
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorNilpotentSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorWithFrame
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveQuotientLifting
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual twisted affine sections of the finite étale adic tower

On an affine chart carrying an original frame of the twist, tensoring
with that frame identifies the native section modules. This comparison
retains the original twisted transition. Its surjectivity, precise adic
kernel, and annihilating ideal power follow from the actual cover tower.

The native twisted sections acquire the canonical quotient-ring action
from this proved annihilation. On a locally Noetherian scheme, they are
projective over that quotient by the actual finite étale coefficient
map. These are the target modules of the quotient-free presentations;
no flatness or kernel identification is supplied as an assumption.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (N : X.Modules) (U : X.affineOpens)

/-- The original twisted sections, with their original affine coefficient action. -/
def twistedAffineSectionModule (n : ℕ) : ModuleCat Γ(X, U) :=
  (moduleSectionsFunctor U).obj (tensor (moduleSheaf f I V n) N)

/-- The original twisted transition on those same native section objects. -/
def twistedAffineSectionTransition (n : ℕ) :
    twistedAffineSectionModule f I V N U (n + 1) →ₗ[Γ(X, U)]
      twistedAffineSectionModule f I V N U n :=
  ((moduleSectionsFunctor U).map (moduleTransition f I V n ▷ N)).hom

variable (t : Γ(N, U)) (ht : IsFrameOn t (U : X.Opens))

include ht

/-- The actual frame identifies untwisted and twisted native sections. -/
def affineTensorFrameSectionsEquiv (n : ℕ) :
    affineSectionModule f I V U n ≃ₗ[Γ(X, U)]
      twistedAffineSectionModule f I V N U n := by
  let l : Γ(moduleSheaf f I V n, U) →ₗ[Γ(X, U)] Γ(moduleSheaf f I V n ⊗ N, U) :=
    (tensorSectionsBilin (moduleSheaf f I V n) N U).flip t
  have hres : N.presheaf.map (homOfLE (le_rfl : (U : X.Opens) ≤ U)).op t = t := by
    change N.presheaf.map (𝟙 (op (U : X.Opens))) t = t
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hl : Function.Bijective l := by
    change Function.Bijective (fun x : Γ(moduleSheaf f I V n, U) => tensorSections x t)
    simpa only [hres] using ht.bijective_tensorSections (moduleSheaf f I V n) le_rfl le_rfl
  exact LinearEquiv.ofBijective l hl

/-- The comparison is tensoring with the specified original frame. -/
theorem affineTensorFrameSectionsEquiv_apply (n : ℕ) (x : affineSectionModule f I V U n) :
    affineTensorFrameSectionsEquiv f I V N U t ht n x =
      tensorSections (L := moduleSheaf f I V n) (M := N) x t := rfl

/-- The comparison commutes with the literal cover-induced twisted transition. -/
theorem affineTensorFrameSectionsEquiv_transition (n : ℕ)
    (x : affineSectionModule f I V U (n + 1)) :
    twistedAffineSectionTransition f I V N U n
        (affineTensorFrameSectionsEquiv f I V N U t ht (n + 1) x) =
      affineTensorFrameSectionsEquiv f I V N U t ht n
        (affineSectionTransition f I V U n x) :=
  whiskerRight_app_tensorSections (moduleTransition f I V n) N x t

/-- The same specified ideal power annihilates the original twisted sections. -/
theorem twistedAffineSections_annihilated (n : ℕ) :
    (sectionsIdeal f I U) ^ (n + 1) •
      (⊤ : Submodule Γ(X, U) (twistedAffineSectionModule f I V N U n)) = ⊥ :=
  ht.smul_top_tensor_eq_bot (M := moduleSheaf f I V n) le_rfl le_rfl
    ((sectionsIdeal f I U) ^ (n + 1)) (moduleSheaf_sections_annihilated f I V n U)

/-- The quotient action is justified by actual annihilation, before being constructed. -/
theorem twistedAffineSections_isTorsionBySet (n : ℕ) :
    Module.IsTorsionBySet Γ(X, U) (twistedAffineSectionModule f I V N U n)
      ((sectionsIdeal f I U) ^ (n + 1) : Ideal Γ(X, U)) := by
  intro x a
  apply (Submodule.mem_bot Γ(X, U)).mp
  rw [← twistedAffineSections_annihilated f I V N U t ht n]
  exact Submodule.smul_mem_smul a.property Submodule.mem_top

/-- The canonical coefficient-quotient action on the original twisted sections. -/
@[instance_reducible]
def twistedAffineSectionQuotientModule (n : ℕ) :
    Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (twistedAffineSectionModule f I V N U n) :=
  (twistedAffineSections_isTorsionBySet f I V N U t ht n).module

/-- The supplied quotient action extends the original native coefficient action. -/
theorem twistedAffineSectionQuotient_isScalarTower (n : ℕ) :
    let _ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (twistedAffineSectionModule f I V N U n) :=
      twistedAffineSectionQuotientModule f I V N U t ht n
    IsScalarTower Γ(X, U) (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (twistedAffineSectionModule f I V N U n) := by
  intro _moduleQ
  exact (twistedAffineSections_isTorsionBySet f I V N U t ht n).isScalarTower

/-- Finiteness is transported from the actual finite cover, with the same original scalars. -/
theorem twistedAffineSections_finite (n : ℕ) :
    Module.Finite Γ(X, U) (twistedAffineSectionModule f I V N U n) := by
  have : Module.Finite Γ(X, U) (affineSectionModule f I V U n) :=
    moduleSheaf_finite_sections f I V n U U.property
  exact Module.Finite.equiv (affineTensorFrameSectionsEquiv f I V N U t ht n)

/-- These actual twisted sections are projective over their prescribed coefficient quotient. -/
theorem twistedAffineSectionQuotient_projective [IsLocallyNoetherian X] (n : ℕ) :
    let _ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (twistedAffineSectionModule f I V N U n) :=
      twistedAffineSectionQuotientModule f I V N U t ht n
    Module.Projective (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (twistedAffineSectionModule f I V N U n) := by
  intro _moduleQ
  let Q := Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)
  let _moduleP : Module Q (affineSectionModule f I V U n) :=
    affineSectionQuotientModule f I V U n
  have : IsScalarTower Γ(X, U) Q (affineSectionModule f I V U n) :=
    affineSectionQuotient_isScalarTower f I V U n
  have : IsScalarTower Γ(X, U) Q (twistedAffineSectionModule f I V N U n) :=
    twistedAffineSectionQuotient_isScalarTower f I V N U t ht n
  have : Module.Projective Q (affineSectionModule f I V U n) :=
    affineSectionQuotient_projective f I V U n
  let e := affineTensorFrameSectionsEquiv f I V N U t ht n
  let eQ : affineSectionModule f I V U n ≃ₗ[Q]
      twistedAffineSectionModule f I V N U n :=
    LinearEquiv.ofBijective
      (AdicModuleSystem.overQuotientLinearMap ((sectionsIdeal f I U) ^ (n + 1))
        e.toLinearMap) e.bijective
  exact Module.Projective.of_equiv' eQ

/-- The original twisted transition is surjective on this affine frame chart. -/
theorem twistedAffineSectionTransition_surjective (n : ℕ) :
    Function.Surjective (twistedAffineSectionTransition f I V N U n) := by
  let e := affineTensorFrameSectionsEquiv f I V N U t ht n
  let e' := affineTensorFrameSectionsEquiv f I V N U t ht (n + 1)
  intro z
  obtain ⟨x, hx⟩ := moduleTransition_app_surjective f I V n U U.property (e.symm z)
  refine ⟨e' x, ?_⟩
  exact (affineTensorFrameSectionsEquiv_transition f I V N U t ht n x).trans
    ((congrArg e hx).trans (e.apply_symm_apply z))

/-- The kernel is exactly the prescribed ideal power in the original twisted source. -/
theorem twistedAffineSectionTransition_ker (n : ℕ) :
    (twistedAffineSectionTransition f I V N U n).ker =
      (sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (twistedAffineSectionModule f I V N U (n + 1))) := by
  apply le_antisymm
  · exact ht.whiskerRight_app_ker_le_smul le_rfl le_rfl (moduleTransition f I V n)
      ((sectionsIdeal f I U) ^ (n + 1)) (moduleTransition_app_ker f I V n U U.property).le
  · apply Submodule.smul_le.mpr
    intro a ha x _hx
    apply LinearMap.mem_ker.mpr
    exact ((twistedAffineSectionTransition f I V N U n).map_smul a x).trans
      (twistedAffineSections_isTorsionBySet f I V N U t ht n
        (x := twistedAffineSectionTransition f I V N U n x) (a := ⟨a, ha⟩))

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
