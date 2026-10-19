/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.SchemeTheory.RingTheory.Polynomial.Macaulay
import Nyll.AlgebraicCurves.Foundations.Polynomial.MacaulayMonomials
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceEq
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceSuccLeMacaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MacaulayMonomialSubspace

/-!
# Mv Polynomial forall finrank piece succ eq macaulay Pow of finrank piece succ eq macaulay
Pow
-/

section ProofImplementation

open _root_.Nat.Macaulay _root_.MvPolynomial.Macaulay

namespace AlgebraicCurves.Foundations.Polynomial.Proofs.MacaulayGrowthPersistence

open MvPolynomial AlgebraicGeometry.HilbertFunctor

namespace PERSISTSOL

variable (n : ℕ)

theorem macaulayPow_choose (δ : ℕ) :
    Nat.macaulayPow (δ + 1) ((n + (δ + 1)).choose n) = (n + (δ + 2)).choose n := by
  have ha : (n + (δ + 1)).choose n = (n + (δ + 1)).choose (δ + 1) := Nat.choose_symm_add
  have ht : top δ ((n + (δ + 1)).choose n) = n + (δ + 1) := by
    refine top_eq_of δ _ (n + (δ + 1)) (by rw [ha]) ?_
    rw [ha, Nat.choose_succ_succ' (n + (δ + 1)) δ]
    have : 0 < (n + (δ + 1)).choose δ := Nat.choose_pos (by omega)
    omega
  have hr : rem δ ((n + (δ + 1)).choose n) = 0 := by
    rw [rem, ht, ha, Nat.sub_self]
  rw [macaulayPow_succ, ht, hr, macaulayPow_zero_right, add_zero,
    show n + (δ + 1) + 1 = n + (δ + 2) by omega]
  exact Nat.choose_symm_add.symm

theorem finrank_piece_le (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K (piece J e) ≤ (n + e).choose n := by
  classical
  have h0 : Module.finrank K (piece (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) e) = (Mon n e).card
    := by
    refine finrank_piece_eq_card n K ⊥ e (Mon n e) (fun m hm => (mem_Mon n e m).1 hm) fun p hp => ?_
    rw [Ideal.mem_bot]
    constructor
    · rintro rfl m _; simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · intro h
      ext m
      rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_cases hm : m ∈ p.support
      · exact h m ((mem_Mon n e m).2 (degree_eq_of_mem_support n K hp hm))
      · exact notMem_support_iff.1 hm
  rw [card_Mon] at h0
  let V := homogeneousSubmodule (Fin (n + 1)) K e
  have hbot : Submodule.comap V.subtype ((⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)).restrictScalars
    K) = ⊥ := by
    rw [Submodule.restrictScalars_bot, Submodule.comap_bot, Submodule.ker_subtype]
  let e₀ : piece (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) e ≃ₗ[K] ↥V :=
    Submodule.quotEquivOfEqBot _ hbot
  have hV : Module.finrank K ↥V = (n + e).choose n := by rw [← e₀.finrank_eq, h0]
  have : Module.Finite K ↥V :=
    Module.finite_of_finrank_pos (by rw [hV]; exact Nat.choose_pos (by omega))
  rw [← hV]
  exact Submodule.finrank_quotient_le _

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem homogeneousComponent_mem_of_span (K : Type) [Field K] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span
      s) :
    ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have hhom : (Ideal.span s).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
    Ideal.homogeneous_span _ _ fun p hp => ⟨d, (mem_homogeneousSubmodule d p).2 (hs p hp)⟩
  intro p hp i
  have := hhom i hp
  rwa [← DirectSum.Decomposition.decompose'_eq, MvPolynomial.decomposition.decompose'_apply] at this

end PERSISTSOL

attribute [local simp]
  MvPolynomial.Macaulay.mem_Mon
attribute [local simp] MvPolynomial.Macaulay.var_apply
attribute [local simp] MvPolynomial.Macaulay.degree_var
attribute [local simp] MvPolynomial.Macaulay.shift_empty


open PERSISTSOL in
theorem
  _root_.MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∀ e : ℕ, m ≤ e → Module.finrank K (piece J (e + 1)) = Nat.macaulayPow e (Module.finrank K
      (piece J e)) := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  let g : ℕ → ℕ := fun k => Nat.rec (Module.finrank K (piece J (m' + 1))) (fun k b =>
    Nat.macaulayPow (m' + 1 + k) b) k
  have g_zero : g 0 = Module.finrank K (piece J (m' + 1)) := rfl
  have g_succ : ∀ k, g (k + 1) = Nat.macaulayPow (m' + 1 + k) (g k) := fun k => rfl
  let h : ℕ → ℕ := fun e => g (e - (m' + 1))
  have h_m : h (m' + 1) = Module.finrank K (piece J (m' + 1)) := by
    change g _ = _; rw [Nat.sub_self]; rfl
  have h_succ : ∀ e, m' + 1 ≤ e → h (e + 1) = Nat.macaulayPow e (h e) := by
    intro e he
    change g (e + 1 - (m' + 1)) = Nat.macaulayPow e (g (e - (m' + 1)))
    rw [show e + 1 - (m' + 1) = (e - (m' + 1)) + 1
      by omega, g_succ, show m' + 1 + (e - (m' + 1)) = e by omega]
  have g_le : ∀ k, g k ≤ (n + (m' + 1 + k)).choose n := by
    intro k
    induction k with
    | zero => rw [g_zero, add_zero]; exact finrank_piece_le n K J _
    | succ k ih =>
      rw [g_succ]
      refine (macaulayPow_mono _ ih).trans ?_
      rw [show m' + 1 + k = (m' + k) + 1 by omega, macaulayPow_choose,
        show n + (m' + 1 + (k + 1)) = n + (m' + k + 2) by omega]
  have h_le : ∀ e, m' + 1 ≤ e → h e ≤ (n + e).choose n := by
    intro e he
    have := g_le (e - (m' + 1))
    rwa [show m' + 1 + (e - (m' + 1)) = e by omega] at this
  have key := MvPolynomial.finrank_piece_eq_of_maximal_growth n (m' + 1) h
    (fun e he K' _ J' hJ' hfin => by
      rw [h_succ e he, ← hfin]
      exact MvPolynomial.finrank_piece_succ_le_macaulayPow n e (by omega) K' J'
        (homogeneousComponent_mem_of_span n K' e J' hJ'))
    (fun e he => by
      obtain ⟨J', hJ', h1, h2⟩ :=
        MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow n
          e (by omega)
          (h e) (h_le e he) K
      exact ⟨K, inferInstance, J', hJ', h1, by rw [h2, h_succ e he]⟩)
    K J hJ h_m.symm (by rw [h_succ _ le_rfl, h_m]; exact hmax)
  intro e he
  rw [key (e + 1) (by omega), key e he, h_succ e he]
end AlgebraicCurves.Foundations.Polynomial.Proofs.MacaulayGrowthPersistence
end ProofImplementation
