/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveSyzygyVanishing
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyGeneration
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyGlobalLifts
public import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionGlobalGeneration
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Compatible second generators on the original closed projective family

Choose finite generators of a sufficiently positive twist of the first
native syzygy. The actual uniform Rees bound lifts each generator through
all original syzygy transitions. The resulting maps have one fixed finite
free source, commute with every transition, and generate every stage by
the proved native nilpotent quotient criterion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (j ≫ π R n) I 0))
  (d : ℕ) (K : Type u) [Finite K]
  (α : ∀ a : ℕ, (show Y.Modules from SheafOfModules.free K) ⟶
    moduleSheaf (j ≫ π R n) I V a ⊗
      ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d)
  (hα : ∀ a : ℕ, α (a + 1) ≫
    (moduleTransition (j ≫ π R n) I V a ▷
      ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d) = α a)
  (hgen : ∀ a : ℕ, Epi (α a))

include hgen in
/-- A single finite free source presents every sufficiently twisted
native syzygy, through maps compatible with the original transitions. -/
theorem exists_closedProjective_syzygy_twisting_bound_compatible_presentations :
    let L : Y.Modules := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    let _ : (L.tensorPow d).IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j d
    let M : ℕ → Y.Modules := fun a => levelPresentationKernel (j ≫ π R n) I V (L.tensorPow d)
      (show Y.Modules from SheafOfModules.free K) a (α a)
    let q : ∀ a : ℕ, M (a + 1) ⟶ M a := fun a =>
      levelPresentationKernelTransition (j ≫ π R n) I V (L.tensorPow d)
        (show Y.Modules from SheafOfModules.free K) α hα a
    ∃ c : ℕ, ∀ e : ℕ, c ≤ e → ∃ J : Type u, Finite J ∧
      ∃ β : ∀ a : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶ M a ⊗ L.tensorPow e,
        (∀ a : ℕ, Epi (β a)) ∧
        (∀ a : ℕ, β (a + 1) ≫ (q a ▷ L.tensorPow e) = β a) := by
  intro L hLd M q
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π R n)
  have : (SheafOfModules.free (R := Y.ringCatSheaf) K).IsFiniteType := by
    let g := SheafOfModules.free.generatingSections (R := Y.ringCatSheaf) K
    let p := g.localGeneratorsData
    have hp : p.IsFiniteType := by
      constructor
      intro U
      exact ⟨inferInstanceAs (Finite K)⟩
    exact p.isFiniteType hp
  have : (M 0).IsFiniteType :=
    levelPresentationKernel_isFiniteType (j ≫ π R n) I V (L.tensorPow d)
      (show Y.Modules from SheafOfModules.free K) 0 (α 0)
  have hL : IsInvertible L := IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  obtain ⟨c₀, h₀⟩ := exists_closedImmersion_twisting_bound_finiteFree_epi R n j (M 0)
  obtain ⟨c₁, h₁⟩ := exists_closedProjective_syzygy_twisting_bound_kernel_HSucc
    R I n j V d K α hα hgen
  refine ⟨max c₀ c₁, ?_⟩
  intro e he
  obtain ⟨J, hJ, φ, hφ⟩ := h₀ e ((le_max_left c₀ c₁).trans he)
  have : Finite J := hJ
  let T : ℕ → Y.Modules := fun a => M a ⊗ L.tensorPow e
  let z : J → Γ(T 0, ⊤) := freeHomTopSectionsEquiv (T 0) J φ
  have hlift : ∀ i : J, ∃ s : ∀ a : ℕ, Γ(T a, ⊤),
      s 0 = z i ∧ ∀ a : ℕ, (q a ▷ L.tensorPow e).app ⊤ (s (a + 1)) = s a := by
    intro i
    exact exists_compatible_levelPresentationKernel_tensorPow_globalSections
      (j ≫ π R n) I V L d K α hα hL hgen
      (stdCoverPullback (A := R) (n := n) j) e
      (fun a => h₁ e ((le_max_right c₀ c₁).trans he) a 0) (z i)
  let s : ∀ a : ℕ, J → Γ(T a, ⊤) := fun a i => (Classical.choose (hlift i)) a
  let β : ∀ a : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶ T a :=
    fun a => (freeHomTopSectionsEquiv (T a) J).symm (s a)
  have hzero : β 0 = φ := by
    apply (freeHomTopSectionsEquiv (T 0) J).injective
    funext i
    exact (congrFun ((freeHomTopSectionsEquiv (T 0) J).apply_symm_apply (s 0)) i).trans
      (Classical.choose_spec (hlift i)).1
  have hβ : ∀ a : ℕ, β (a + 1) ≫ (q a ▷ L.tensorPow e) = β a := by
    intro a
    apply (freeHomTopSectionsEquiv (T a) J).injective
    funext i
    let r : T (a + 1) ⟶ T a := q a ▷ L.tensorPow e
    exact (freeHomTopSectionsEquiv_comp (T (a + 1)) J (β (a + 1)) r i).trans
      ((congrArg (r.app ⊤)
        (congrFun ((freeHomTopSectionsEquiv (T (a + 1)) J).apply_symm_apply (s (a + 1))) i)).trans
        (((Classical.choose_spec (hlift i)).2 a).trans
          (congrFun ((freeHomTopSectionsEquiv (T a) J).apply_symm_apply (s a)) i).symm))
  have hEpi : Epi (β 0) := hzero.symm ▸ hφ
  refine ⟨J, hJ, β, ?_, hβ⟩
  exact levelPresentationKernel_epi_of_compatible_twisted_lifts
    (j ≫ π R n) I V L d K α hα hL hgen
    (show Y.Modules from SheafOfModules.free J) e β hEpi hβ

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
