/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivFD
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivPi
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModulePresentationKerIsFG
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedPresentationShift
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedPresentationVanishing
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistPositiveVanishing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.Linarith

/-!
# Serre vanishing for finitely generated graded modules

For the actual projective Čech complex of a finitely generated graded
module over a Noetherian ring, all positive cohomology groups vanish
after a sufficiently large degree shift. A fixed finite presentation
gives a bound for the free source. Descending induction on cohomological
degree, using finite generation of the actual presentation kernel,
constructs a bound for each positive degree. A common finite upper bound gives one
bound valid in every positive degree.

The existence of the bound is proved here. It is not supplied as a
regularity or vanishing hypothesis. The theorem concerns the graded
module Čech model; applying it to arbitrary coherent formal sheaves also
requires their geometric presentation and compatibility constructions.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The finitely many generator degrees in one presentation give a
uniform vanishing bound for all positive cohomology of its free source. -/
theorem Presentation.exists_twist_bound_subsingleton_H_F
    {D : GradedModule R n} (σ : Presentation D) :
    ∃ b : ℤ, ∀ e : ℤ, b ≤ e → ∀ i : ℕ,
      Subsingleton (H (σ.shift e).F (i + 1)) := by
  let b : ℤ := ∑ k : σ.J, |σ.d₀ k|
  refine ⟨b, ?_⟩
  intro e he i
  have hdegree : ∀ k : σ.J, 0 ≤ e + σ.d₀ k := by
    intro k
    have hbound : |σ.d₀ k| ≤ b :=
      Finset.single_le_sum (fun j _ => abs_nonneg (σ.d₀ j)) (Finset.mem_univ k)
    have hneg : -σ.d₀ k ≤ |σ.d₀ k| := neg_le_abs (σ.d₀ k)
    linarith
  have hcomponent : ∀ k : σ.J, Subsingleton (H (FD R n (e + σ.d₀ k)) (i + 1)) := by
    intro k
    obtain ⟨E⟩ := nonempty_HEquiv_FD R n (e + σ.d₀ k) (i + 1)
    have htwist : Subsingleton (Twist.H R n (e + σ.d₀ k) (i + 1)) :=
      Twist.subsingleton_cohomology_succ_of_nonneg R n (e + σ.d₀ k) (hdegree k) i
    exact ⟨fun x y => E.symm.injective (htwist.elim (E.symm x) (E.symm y))⟩
  obtain ⟨E⟩ := nonempty_HEquiv_pi (fun k : σ.J => FD R n (e + σ.d₀ k)) (i + 1)
  refine ⟨fun x y => E.injective ?_⟩
  funext k
  exact (hcomponent k).elim (E x k) (E y k)

/-- Descending through the actual presentation kernels gives a twist
bound in any prescribed positive cohomological degree. -/
theorem exists_twist_bound_subsingleton_H_succ [IsNoetherianRing R]
    (D : GradedModule R n) (hD : IsFG D) (i : ℕ) :
    ∃ b : ℤ, ∀ e : ℤ, b ≤ e → Subsingleton (H (D.shift e) (i + 1)) := by
  suffices h : ∀ j : ℕ, ∀ E : GradedModule R n, IsFG E →
      ∃ b : ℤ, ∀ e : ℤ, b ≤ e → Subsingleton (H (E.shift e) (j + 1)) from h i D hD
  intro j
  induction j using Nat.strong_decreasing_induction with
  | base =>
      refine ⟨n, ?_⟩
      intro j hj E _hE
      refine ⟨0, ?_⟩
      intro e _he
      exact subsingleton_cohomology_of_lt (E.shift e)
        (Nat.lt_trans hj (Nat.lt_succ_self j))
  | step j ih =>
      intro E hE
      obtain ⟨σ⟩ := hE
      obtain ⟨bK, hK⟩ := ih (j + 1) (Nat.lt_succ_self j) σ.ker
        (Presentation.ker_isFG σ)
      obtain ⟨bF, hF⟩ := Presentation.exists_twist_bound_subsingleton_H_F σ
      refine ⟨max bF bK, ?_⟩
      intro e he
      have hfree : Subsingleton (H (σ.shift e).F (j + 1)) :=
        hF e ((le_max_left bF bK).trans he) j
      have hkernel : Subsingleton (H (σ.shift e).ker (j + 1 + 1)) := by
        rw [Presentation.shift_ker]
        exact hK e ((le_max_right bF bK).trans he)
      exact Presentation.subsingleton_H_succ_of_subsingleton (σ.shift e) j hfree hkernel

/-- Serre vanishing for the graded module Čech model: one constructed
twist bound works for every positive cohomological degree. -/
theorem exists_twist_bound_subsingleton_cohomology_succ [IsNoetherianRing R]
    (D : GradedModule R n) (hD : IsFG D) :
    ∃ b : ℤ, ∀ e : ℤ, b ≤ e → ∀ i : ℕ,
      Subsingleton (H (D.shift e) (i + 1)) := by
  let b : Fin (n + 1) → ℤ := fun k =>
    Classical.choose (exists_twist_bound_subsingleton_H_succ D hD k.val)
  have hb : ∀ k : Fin (n + 1), ∀ e : ℤ, b k ≤ e →
      Subsingleton (H (D.shift e) (k.val + 1)) :=
    fun k => Classical.choose_spec (exists_twist_bound_subsingleton_H_succ D hD k.val)
  refine ⟨∑ k : Fin (n + 1), |b k|, ?_⟩
  intro e he i
  by_cases hi : i < n + 1
  · let k : Fin (n + 1) := ⟨i, hi⟩
    have hsum : |b k| ≤ ∑ j : Fin (n + 1), |b j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (b j)) (Finset.mem_univ k)
    exact hb k e ((le_abs_self (b k)).trans (hsum.trans he))
  · have hni : n < i :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_not_lt hi)
    exact subsingleton_cohomology_of_lt (D.shift e)
      (Nat.lt_trans hni (Nat.lt_succ_self i))

end ProjSpaceCech.GradedModule
