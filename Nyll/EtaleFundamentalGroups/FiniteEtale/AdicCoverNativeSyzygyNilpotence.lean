/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelPresentations
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelFreeSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.Modules.Sections.KernelSections
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientFreeSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Nilpotence on the original closed-level syzygy sections

The actual native syzygy injects into the original closed-level free
source. Its affine sections are therefore annihilated by the original
coefficient ideal power, through the constructed quotient-free section
equivalence. The proof does not choose a frame or require an epimorphic
presentation, and applies to every affine open of the original scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) [L.IsQuasicoherent] (K : Type u) [Finite K]

/-- The native closed-level syzygy is annihilated by the original
coefficient ideal power on every affine open, without a local frame. -/
theorem levelPresentationKernel_sections_annihilated
    (n : ℕ) (α : (show X.Modules from SheafOfModules.free K) ⟶ moduleSheaf f I V n ⊗ L)
    (U : X.affineOpens) :
    (sectionsIdeal f I U) ^ (n + 1) •
      (⊤ : Submodule Γ(X, U)
        Γ(levelPresentationKernel f I V L
          (show X.Modules from SheafOfModules.free K) n α, U)) = ⊥ := by
  let P : X.Modules := SheafOfModules.free K
  let φ : levelPullbackModule f I P n ⟶ moduleSheaf f I V n ⊗ L :=
    levelPresentation f I V L P n α
  let E := kernelSectionsEquiv φ (U : X.Opens)
  let j : Γ(levelPresentationKernel f I V L P n α, U) →ₗ[Γ(X, U)]
      Γ(levelPullbackModule f I P n, U) :=
    (((moduleSectionsFunctor (U : X.Opens)).map φ).hom.ker).subtype.comp E.toLinearMap
  have hj : Function.Injective j := Subtype.val_injective.comp E.injective
  let e : (K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) ≃ₗ[Γ(X, U)]
      Γ(levelPullbackModule f I P n, U) := levelFreeSectionsEquiv f I K U n
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x _hx
  apply (Submodule.mem_bot Γ(X, U)).mpr
  apply hj
  rw [j.map_smul, j.map_zero]
  obtain ⟨c, hc⟩ := e.surjective (j x)
  rw [← hc, ← e.map_smul]
  have hz : a • c = 0 :=
    quotientFree_isTorsionBySet ((sectionsIdeal f I U) ^ (n + 1)) K
      (x := c) (a := ⟨a, ha⟩)
  exact (congrArg e hz).trans e.map_zero

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
