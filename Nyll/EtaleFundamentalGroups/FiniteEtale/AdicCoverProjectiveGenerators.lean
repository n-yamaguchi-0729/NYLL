/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverProjectiveTwistedLifts
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTwistedGeneratingSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafGlobalGeneration
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Order.Lattice

/-!
# Constructed compatible finite generators for the projective cover tower

Take the larger of the actual first-stage generation bound and the
proved uniform global-lifting bound. Lift each member of that finite
first-stage family through every original cover transition. The actual
nilpotent generation theorem then proves that these same finitely many
lifted sections generate every thickening.

The conclusion supplies the original section families, their common
finite index type, the actual epimorphic free-sheaf maps, and compatibility
with the original transitions. None of these are hypotheses.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (π R n) I 0))

/-- Every sufficiently large twist has a constructed finite family of
original global sections generating every stage and compatible with
every original cover transition. -/
theorem exists_projective_twisting_bound_compatible_generators :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∃ J : Type u, Finite J ∧
      ∃ s : ∀ k : ℕ, J → Γ(projectiveTwistedModule R I n V d k, ⊤),
        (∀ k : ℕ, Epi (projectiveTwistedGeneratingMap R I n V d J s k)) ∧
        (∀ (k : ℕ) (j : J),
          (moduleTransition (π R n) I V k ▷ (twistingSheaf R n).tensorPow d).app ⊤
            (s (k + 1) j) = s k j) := by
  obtain ⟨c₀, h₀⟩ :=
    exists_twisting_bound_generatingSections R n (moduleSheaf (π R n) I V 0)
  obtain ⟨c₁, h₁⟩ := exists_projective_twisting_bound_globalLifts R I n V
  refine ⟨max c₀ c₁, ?_⟩
  intro d hd
  obtain ⟨G, hG⟩ := h₀ d ((le_max_left c₀ c₁).trans hd)
  have : G.IsFiniteType := hG
  have hfinite : Finite G.I := SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)
  have hLift : ∀ j : G.I,
      ∃ t : ∀ k : ℕ, Γ(projectiveTwistedModule R I n V d k, ⊤),
        t 0 = (G.s j).val (op ⊤) ∧ ∀ k : ℕ,
          (moduleTransition (π R n) I V k ▷ (twistingSheaf R n).tensorPow d).app ⊤
            (t (k + 1)) = t k :=
    fun j => h₁ d ((le_max_right c₀ c₁).trans hd) ((G.s j).val (op ⊤))
  let t : G.I → (k : ℕ) → Γ(projectiveTwistedModule R I n V d k, ⊤) :=
    fun j => Classical.choose (hLift j)
  let s : (k : ℕ) → G.I → Γ(projectiveTwistedModule R I n V d k, ⊤) := fun k j => t j k
  have hz : ∀ j : G.I, s 0 j = (G.s j).val (op ⊤) :=
    fun j => (Classical.choose_spec (hLift j)).1
  have hs : ∀ (k : ℕ) (j : G.I),
      (moduleTransition (π R n) I V k ▷ (twistingSheaf R n).tensorPow d).app ⊤
        (s (k + 1) j) = s k j :=
    fun k j => (Classical.choose_spec (hLift j)).2 k
  exact ⟨G.I, hfinite, s,
    fun k => projectiveTwistedGeneratingMap_epi R I n V d G s hz hs k, hs⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
