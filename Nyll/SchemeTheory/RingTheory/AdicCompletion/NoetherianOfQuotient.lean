/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.ReesApproximation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Noetherian completion from a Noetherian quotient

If `I` is finitely generated and `R/I` is Noetherian, the `I`-adic
completion is Noetherian. The coefficient ring itself need not be
Noetherian.

The proof first treats a complete ring. For an arbitrary ideal, finite
homogeneous generators in the residual Rees algebra give corrections of
increasing adic order. The partial sums of their coefficients are Cauchy.
Their actual limits express each element of the ideal as a finite linear
combination of the chosen generators. Thus the proof does not assume
that ideals are closed. Applying this construction to the completion and
its actual quotient gives Stacks, Tag 05GH.
-/

noncomputable section

universe u

namespace AdicCompletion

namespace NoetherianCriterion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A complete ring is Noetherian if its defining ideal is finitely
generated and the quotient is Noetherian. The finite generators of each
ideal are obtained by converging the coefficients of Rees approximations.
-/
theorem isNoetherianRing_of_isAdicComplete (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] [IsAdicComplete I R] : IsNoetherianRing R := by
  classical
  apply (isNoetherianRing_iff_ideal_fg R).mpr
  intro J
  obtain ⟨r, g, c, hgJ, happrox⟩ := exists_finite_approximation I hI J
  apply Submodule.fg_iff_exists_fin_generating_family.mpr
  refine ⟨r, g, le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgJ i
  · intro x hxJ
    let P (n : ℕ) := {y : R // y ∈ J ∧ y ∈ I ^ n}
    let a (n : ℕ) (y : P n) : Fin r → R :=
      (happrox n y.val y.property.1 y.property.2).choose
    have ha : ∀ (n : ℕ) (y : P n),
        (∀ i, a n y i ∈ I ^ (n - c)) ∧
          y.val - ∑ i, a n y i * g i ∈ I ^ (n + 1) := by
      intro n y
      exact (happrox n y.val y.property.1 y.property.2).choose_spec
    let step (n : ℕ) (y : P n) : P (n + 1) :=
      ⟨y.val - ∑ i, a n y i * g i,
        J.sub_mem y.property.1 (J.sum_mem fun i _ => J.mul_mem_left (a n y i) (hgJ i)),
        (ha n y).2⟩
    let residual : (n : ℕ) → P n :=
      fun n => Nat.rec (motive := P)
        ⟨x, hxJ, by
          rw [pow_zero, Ideal.one_eq_top]
          exact (show x ∈ (⊤ : Ideal R) from Submodule.mem_top)⟩ step n
    let correction (n : ℕ) : Fin r → R := a n (residual n)
    have hcorrection : ∀ n i, correction n i ∈ I ^ (n - c) := by
      intro n i
      exact (ha n (residual n)).1 i
    have hstep : ∀ n, (residual (n + 1)).val =
        (residual n).val - ∑ i, correction n i * g i := fun _ => rfl
    let coefficientsPartial : ℕ → Fin r → R :=
      fun n => Nat.rec (fun _ => 0) (fun n b i => b i + correction n i) n
    have hpartial : ∀ n i,
        coefficientsPartial (n + 1) i = coefficientsPartial n i + correction n i :=
      fun _ _ => rfl
    have hresidual : ∀ n, (residual n).val = x - ∑ i, coefficientsPartial n i * g i := by
      intro n
      induction n with
      | zero =>
          change x = x - ∑ i, (0 : R) * g i
          simp only [zero_mul, Finset.sum_const_zero, sub_zero]
      | succ n ih =>
          rw [hstep, ih]
          simp only [hpartial, add_mul, Finset.sum_add_distrib]
          ring
    have hcauchy : ∀ i, IsAdicCauchy I R (fun n => coefficientsPartial (n + c) i) := by
      intro i
      apply (isAdicCauchy_iff I R (fun n => coefficientsPartial (n + c) i)).mpr
      intro n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have hc : correction (n + c) i ∈ I ^ n := by
        simpa only [Nat.add_sub_cancel] using hcorrection (n + c) i
      have hp : coefficientsPartial (n + 1 + c) i =
          coefficientsPartial (n + c) i + correction (n + c) i := by
        rw [Nat.add_right_comm n 1 c, hpartial]
      have hd : coefficientsPartial (n + c) i - coefficientsPartial (n + 1 + c) i =
          -correction (n + c) i := by
        rw [hp]
        ring
      rw [hd]
      exact (I ^ n).neg_mem hc
    choose b hb using fun i : Fin r =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete I R) (hcauchy i)
    have hbmem : ∀ i n, coefficientsPartial (n + c) i - b i ∈ I ^ n := by
      intro i n
      have h := (SModEq.sub_mem).mp (hb i n)
      rw [smul_eq_mul, Ideal.mul_top] at h
      exact h
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    refine ⟨b, ?_⟩
    symm
    apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have hr : x - ∑ i, coefficientsPartial (n + c) i * g i ∈ I ^ n := by
      rw [← hresidual]
      exact Ideal.pow_le_pow_right (Nat.le_add_right n c) (residual (n + c)).property.2
    have hl : ∑ i, (coefficientsPartial (n + c) i - b i) * g i ∈ I ^ n :=
      (I ^ n).sum_mem fun i _ => Ideal.mul_mem_right (g i) (I ^ n) (hbmem i n)
    have hsum : x - ∑ i, b i * g i =
        (x - ∑ i, coefficientsPartial (n + c) i * g i) +
          ∑ i, (coefficientsPartial (n + c) i - b i) * g i := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hsum]
    exact (I ^ n).add_mem hr hl

end NoetherianCriterion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Completion is Noetherian under finite generation of the ideal and
Noetherianity of the quotient, even when the original ring is not known
to be Noetherian. -/
theorem isNoetherianRing_of_noetherian_quotient (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing (AdicCompletion I R) := by
  let S := AdicCompletion I R
  let J : Ideal S := I.map (algebraMap R S)
  have hJ : J.FG := hI.map (algebraMap R S)
  have : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I hI
  have : IsNoetherianRing (S ⧸ J) := by
    change IsNoetherianRing
      (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R)))
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I hI]
    exact isNoetherianRing_of_ringEquiv (R ⧸ I)
      ((AdicCompletion.evalOneₐ I).toRingHom.quotientKerEquivOfSurjective
        (AdicCompletion.evalOneₐ_surjective I)).symm
  exact NoetherianCriterion.isNoetherianRing_of_isAdicComplete J hJ

end AdicCompletion
