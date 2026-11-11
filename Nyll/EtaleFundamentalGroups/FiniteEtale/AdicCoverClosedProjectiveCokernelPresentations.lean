/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveSyzygyPresentations
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygyCokernels
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Actual compatible cokernel presentations on the closed projective family

The constructed second generators compose with the original kernel
inclusions. This produces compatible relation maps with fixed finite
source, whose actual cokernels recover every original cover module after
the two prescribed twists. Each recovery keeps the original quotient map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

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

include hα hgen in
/-- Every sufficiently large second twist has compatible relation maps
whose cokernels recover all original cover stages, with their actual
quotient maps retained. Both generator index types remain finite. -/
theorem exists_closedProjective_twisting_bound_compatible_cokernel_presentations :
    let L : Y.Modules := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    let _ : (L.tensorPow d).IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j d
    ∃ c : ℕ, ∀ e : ℕ, c ≤ e → ∃ J : Type u, Finite J ∧
      ∃ θ : ∀ a : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶
          levelPullbackModule (j ≫ π R n) I
            (show Y.Modules from SheafOfModules.free K) a ⊗ L.tensorPow e,
        (∀ a : ℕ, θ (a + 1) ≫
          (levelPullbackTransition (j ≫ π R n) I
            (show Y.Modules from SheafOfModules.free K) a ▷ L.tensorPow e) = θ a) ∧
        ∀ a : ℕ, ∃ E : cokernel (θ a) ≅
            (moduleSheaf (j ≫ π R n) I V a ⊗ L.tensorPow d) ⊗ L.tensorPow e,
          cokernel.π (θ a) ≫ E.hom =
            (levelPresentation (j ≫ π R n) I V (L.tensorPow d)
              (show Y.Modules from SheafOfModules.free K) a (α a) ▷ L.tensorPow e) := by
  intro L hLd
  obtain ⟨c, hc⟩ := exists_closedProjective_syzygy_twisting_bound_compatible_presentations
    R I n j V d K α hα hgen
  refine ⟨c, ?_⟩
  intro e he
  obtain ⟨J, hJ, β, hgenβ, hβ⟩ := hc e he
  have : Finite J := hJ
  let P : Y.Modules := SheafOfModules.free K
  let Q : Y.Modules := SheafOfModules.free J
  let θ : ∀ a : ℕ, Q ⟶ levelPullbackModule (j ≫ π R n) I P a ⊗ L.tensorPow e :=
    fun a => levelSyzygyPresentation (j ≫ π R n) I V (L.tensorPow d) P
      (L.tensorPow e) Q a (α a) (β a)
  refine ⟨J, hJ, θ, ?_, ?_⟩
  · exact fun a => levelSyzygyPresentation_transition (j ≫ π R n) I V
      (L.tensorPow d) P (L.tensorPow e) Q α hα β hβ a
  · intro a
    have : Epi (α a) := hgen a
    have : Epi (β a) := hgenβ a
    exact exists_levelSyzygyPresentation_cokernelIso (j ≫ π R n) I V
      (L.tensorPow d) P (L.tensorPow e) Q a (α a) (β a)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
