/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModulePresentationFiniteH
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModulePresentationKerIsFG
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedPresentationShift
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedSerreVanishing
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedGlobalSections
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedFreeGlobalSections
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.Linarith

/-!
# Lifting global Čech sections to homogeneous numerators

The degree pieces of a finitely generated graded module are finite over
the coefficient ring, by the actual homogeneous presentation. Over a
Noetherian ring, every sufficiently positive global Čech section lifts
to a numerator in its homogeneous degree. Serre vanishing kills the
connecting class in the first cohomology of the presentation kernel;
the remaining lift through the free source is a polynomial numerator.

Both the section and its numerator are constructed from the original
presentation. No uniform regularity or eventual surjectivity is assumed.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

open AlgebraicCurves.Cohomology.Cech.Proofs
open ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.ProjSpaceCech.GradedModule

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Every homogeneous degree piece of a finitely generated graded module
is finite over the coefficient ring. -/
theorem finite_grade (D : GradedModule R n) (hD : IsFG D) (e : ℤ) :
    Module.Finite R (D.grade e) := by
  obtain ⟨σ⟩ := hD
  have hfree : (σ.F.grade e).FG := by
    change (Submodule.pi Set.univ (fun k : σ.J => freeGrade R n (e + σ.d₀ k))).FG
    apply Submodule.fg_pi
    intro k
    by_cases hk : 0 ≤ e + σ.d₀ k
    · rw [freeGrade_of_nonneg R n hk]
      exact MvPolynomial.homogeneousSubmodule_fg (Fin (n + 1)) R (e + σ.d₀ k).toNat
    · rw [freeGrade, ite_eq_right hk]
      exact Submodule.fg_bot
  have himage : (σ.F.grade e).map σ.hom.toLinearMap = D.grade e := by
    apply le_antisymm
    · rintro m ⟨a, ha, rfl⟩
      exact σ.hom.mem_grade e a ha
    · intro m hm
      obtain ⟨a, ha, ham⟩ := σ.surj e m hm
      exact ⟨a, ha, ham⟩
  apply Module.Finite.of_fg
  rw [← himage]
  exact hfree.map σ.hom.toLinearMap

/-- In sufficiently large homogeneous degree, every global Čech section
of a finitely generated graded module has an actual numerator. -/
theorem exists_twist_bound_surjective_augmentation [IsNoetherianRing R]
    (D : GradedModule R n) (hD : IsFG D) :
    ∃ b : ℤ, ∀ e : ℤ, b ≤ e → Function.Surjective (augmentation (D.shift e)) := by
  obtain ⟨σ⟩ := hD
  obtain ⟨bK, hK⟩ := exists_twist_bound_subsingleton_H_succ σ.ker
    (Presentation.ker_isFG σ) 0
  let bF : ℤ := ∑ k : σ.J, |σ.d₀ k|
  refine ⟨max bK bF, ?_⟩
  intro e he
  have hkernel : Subsingleton (H (σ.shift e).ker 1) := by
    rw [Presentation.shift_ker]
    exact hK e ((le_max_left bK bF).trans he)
  have hfree : Function.Surjective (augmentation (σ.shift e).F) := by
    apply augmentation_pi_surjective
    intro k
    apply augmentation_FD_surjective
    change 0 ≤ e + σ.d₀ k
    have hbound : |σ.d₀ k| ≤ bF :=
      Finset.single_le_sum (fun j _ => abs_nonneg (σ.d₀ j)) (Finset.mem_univ k)
    have heF : bF ≤ e := (le_max_right bK bF).trans he
    have hneg : -σ.d₀ k ≤ |σ.d₀ k| := neg_le_abs (σ.d₀ k)
    linarith
  intro z
  have hdelta : delta0 (σ.shift e) 0 z = 0 :=
    hkernel.elim (delta0 (σ.shift e) 0 z) 0
  obtain ⟨w, hw⟩ := ker_delta0_le (σ.shift e) 0 (LinearMap.mem_ker.mpr hdelta)
  obtain ⟨m, hm⟩ := hfree w
  refine ⟨(σ.shift e).hom.gradeMap 0 m, ?_⟩
  calc
    augmentation (D.shift e) ((σ.shift e).hom.gradeMap 0 m) =
        Hom.HMap (σ.shift e).hom 0 (augmentation (σ.shift e).F m) :=
      (augmentation_naturality (σ.shift e).hom m).symm
    _ = Hom.HMap (σ.shift e).hom 0 w := congrArg (Hom.HMap (σ.shift e).hom 0) hm
    _ = z := hw

end ProjSpaceCech.GradedModule
