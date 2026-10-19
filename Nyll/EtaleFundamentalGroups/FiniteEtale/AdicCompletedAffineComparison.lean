/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedPullbackSections
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ReductionSystemComparison
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Operations

/-!
# Completion of original affine sections from their closed restrictions

On an actual affine open, the original adjunction units of a
quasicoherent module are surjective and have exactly the extended
ideal powers as kernels. Completing these same linear maps therefore
identifies the completion of the original section module with the
compatible completed closed-level sections, linearly over the
completed original coefficient ring.

The comparison retains the original module, every original transition,
and the completion of every original restriction as its components.
It requires only finite generation of the extended ideal.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A) (M : X.Modules) (U : X.affineOpens)

/-- The original affine closed restriction, with its original coefficient action. -/
def levelPullbackAffineUnit (n : ℕ) :
    Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(levelPullbackModule f I M n, U.1) :=
  ((levelPullbackUnit f I M n).val.app (op U.1)).hom

/-- The original closed-level transition on the same affine section modules. -/
def levelPullbackAffineTransition (n : ℕ) :
    Γ(levelPullbackModule f I M (n + 1), U.1) →ₗ[Γ(X, U.1)]
      Γ(levelPullbackModule f I M n, U.1) :=
  ((levelPullbackTransition f I M n).val.app (op U.1)).hom

/-- The original affine maps form the original reduction system. -/
theorem levelPullbackAffineUnit_transition (n : ℕ) :
    (levelPullbackAffineTransition f I M U n).comp
      (levelPullbackAffineUnit f I M U (n + 1)) = levelPullbackAffineUnit f I M U n := by
  let F : X.Modules ⥤ ModuleCat Γ(X, U.1) := Scheme.Modules.moduleSectionsFunctor U.1
  let a : M ⟶ levelPullbackModule f I M (n + 1) := levelPullbackUnit f I M (n + 1)
  let b : levelPullbackModule f I M (n + 1) ⟶ levelPullbackModule f I M n :=
    levelPullbackTransition f I M n
  have h : F.map a ≫ F.map b = F.map (levelPullbackUnit f I M n) :=
    (F.map_comp a b).symm.trans (congrArg F.map (levelPullbackUnit_transition f I M n))
  exact (ModuleCat.hom_comp (F.map a) (F.map b)).symm.trans
    (congrArg (fun k : F.obj M ⟶ F.obj (levelPullbackModule f I M n) => k.hom) h)

/-- Original completed affine closed-level sections over the completed original ring. -/
def completedLevelAffineSections :
    Submodule (AdicCompletion (sectionsIdeal f I U.1) Γ(X, U.1))
      ((n : ℕ) → AdicCompletion (sectionsIdeal f I U.1)
        Γ(levelPullbackModule f I M n, U.1)) :=
  AdicModuleSystem.sections
    (fun n => AdicCompletion (sectionsIdeal f I U.1) Γ(levelPullbackModule f I M n, U.1))
    (fun n => AdicCompletion.map (sectionsIdeal f I U.1)
      (levelPullbackAffineTransition f I M U n))

/-- Complete the actual original affine restriction maps. -/
def completedLevelAffineMap :
    AdicCompletion (sectionsIdeal f I U.1) Γ(M, U.1) →ₗ[
      AdicCompletion (sectionsIdeal f I U.1) Γ(X, U.1)] completedLevelAffineSections f I M U :=
  AdicModuleSystem.completedReductionSectionsMap (sectionsIdeal f I U.1)
    (fun n => Γ(levelPullbackModule f I M n, U.1))
    (levelPullbackAffineTransition f I M U) (levelPullbackAffineUnit f I M U)
    (levelPullbackAffineUnit_transition f I M U)

/-- Every component is the completion of the corresponding original affine restriction. -/
theorem completedLevelAffineMap_apply
    (x : AdicCompletion (sectionsIdeal f I U.1) Γ(M, U.1)) (n : ℕ) :
    (completedLevelAffineMap f I M U x).val n =
      AdicCompletion.map (sectionsIdeal f I U.1) (levelPullbackAffineUnit f I M U n) x :=
  rfl

/-- At an original section the comparison retains the literal original adjunction unit. -/
theorem completedLevelAffineMap_of (x : Γ(M, U.1)) (n : ℕ) :
    (completedLevelAffineMap f I M U (AdicCompletion.of (sectionsIdeal f I U.1)
      Γ(M, U.1) x)).val n =
      AdicCompletion.of (sectionsIdeal f I U.1) Γ(levelPullbackModule f I M n, U.1)
        ((levelPullbackUnit f I M n).app U.1 x) :=
  AdicCompletion.map_of (sectionsIdeal f I U.1) (levelPullbackAffineUnit f I M U n) x

variable [M.IsQuasicoherent]

private theorem affineUnit_kernel (n : ℕ) :
    (levelPullbackAffineUnit f I M U n).ker =
      (sectionsIdeal f I U.1) ^ (n + 1) • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  apply Submodule.ext
  intro x
  exact levelPullbackUnit_app_eq_zero_iff f I M n U x

/-- Actual affine quotient kernels make the completed original restriction map bijective. -/
theorem completedLevelAffineMap_bijective (hfg : (sectionsIdeal f I U.1).FG) :
    Function.Bijective (completedLevelAffineMap f I M U) :=
  AdicModuleSystem.completedReductionSectionsMap_bijective (sectionsIdeal f I U.1)
    (fun n => Γ(levelPullbackModule f I M n, U.1))
    (levelPullbackAffineTransition f I M U) (levelPullbackAffineUnit f I M U)
    (levelPullbackAffineUnit_transition f I M U)
    (fun n => levelPullbackUnit_app_surjective f I M n U)
    (affineUnit_kernel f I M U) hfg

/-- The completion comparison constructed from the original affine restriction maps. -/
def completedLevelAffineEquiv (hfg : (sectionsIdeal f I U.1).FG) :
    AdicCompletion (sectionsIdeal f I U.1) Γ(M, U.1) ≃ₗ[
      AdicCompletion (sectionsIdeal f I U.1) Γ(X, U.1)] completedLevelAffineSections f I M U :=
  LinearEquiv.ofBijective (completedLevelAffineMap f I M U)
    (completedLevelAffineMap_bijective f I M U hfg)

/-- The constructed completed-ring equivalence retains every original affine component. -/
theorem completedLevelAffineEquiv_apply (hfg : (sectionsIdeal f I U.1).FG)
    (x : AdicCompletion (sectionsIdeal f I U.1) Γ(M, U.1)) (n : ℕ) :
    (completedLevelAffineEquiv f I M U hfg x).val n =
      AdicCompletion.map (sectionsIdeal f I U.1) (levelPullbackAffineUnit f I M U n) x :=
  rfl

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
