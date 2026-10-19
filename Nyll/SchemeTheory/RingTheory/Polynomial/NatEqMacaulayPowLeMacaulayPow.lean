/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Batteries.Tactic.Init
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Operations
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.PiLex
import Mathlib.Order.RelClasses
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Nyll.SchemeTheory.RingTheory.Polynomial.Macaulay

/-!
# Nat exists forall eq macaulay Pow of forall le macaulay Pow
-/

section ProofImplementation

open _root_.Nat.Macaulay

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow

namespace GotzNum

/-- The sequence obtained recursively from the top indices and remainders of the binomial
expansion. -/
def vec : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | d + 1, a, 0 => top d a - d
  | d + 1, a, p + 1 => vec d (rem d a) p

@[scoped simp] theorem vec_zero (a p : ℕ) : vec 0 a p = 0 := rfl
@[scoped simp] theorem vec_succ_zero (d a : ℕ) : vec (d + 1) a 0 = top d a - d := rfl
@[scoped simp] theorem vec_succ_succ (d a p : ℕ) : vec (d + 1) a (p + 1) = vec d (rem d a) p := rfl

theorem vec_macaulayPow : ∀ (d a : ℕ), vec (d + 1) (Nat.macaulayPow d a) = vec d a
  | 0, a => by
      funext p
      cases p with
      | zero =>
          simp only [macaulayPow_zero, vec_succ_zero, top_zero_right, Nat.sub_self, vec_zero]
      | succ p => simp only [vec_succ_succ, vec_zero]
  | d + 1, a => by
      funext p
      cases p with
      | zero =>
          simp only [vec_succ_zero, top_macaulayPow]
          omega
      | succ p =>
          simp only [vec_succ_succ, rem_macaulayPow]
          rw [vec_macaulayPow d (rem d a)]

theorem vec_eq_zero_of_le : ∀ (d a p : ℕ), d ≤ p → vec d a p = 0
  | 0, _, _, _ => rfl
  | d + 1, a, 0, h => by omega
  | d + 1, a, p + 1, h => by
      simp only [vec_succ_succ]; exact vec_eq_zero_of_le d _ p (by omega)

theorem vec_succ_le : ∀ (d a p : ℕ), vec d a (p + 1) ≤ vec d a p
  | 0, _, _ => le_rfl
  | d + 1, a, p + 1 => by
      simp only [vec_succ_succ]; exact vec_succ_le d _ p
  | 0 + 1, a, 0 => Nat.zero_le _
  | (e + 1) + 1, a, 0 => by
      simp only [vec_succ_succ, vec_succ_zero]
      have h := rem_lt (e + 1) a
      have := top_lt_of_lt_choose e (rem (e + 1) a) (top (e + 1) a) h
      omega

theorem vec_antitone (d a : ℕ) : Antitone (vec d a) :=
  antitone_nat_of_succ_le (vec_succ_le d a)

theorem lex_vec_of_lt : ∀ (d : ℕ) {a b : ℕ}, a < b →
    Pi.Lex (· < ·) (fun {_} => (· < ·)) (vec (d + 1) a) (vec (d + 1) b)
  | 0, a, b, h => ⟨0, fun j hj => (Nat.not_lt_zero j hj).elim,
      by simpa only [vec_succ_zero, top_zero_left, Nat.sub_zero] using h⟩
  | d + 1, a, b, h => by
      rcases lt_trichotomy (top (d + 1) a) (top (d + 1) b) with ht | ht | ht
      · refine ⟨0, fun j hj => (Nat.not_lt_zero j hj).elim, ?_⟩
        have := d_le_top (d + 1) a
        simp only [vec_succ_zero]
        omega
      · have hrem : rem (d + 1) a < rem (d + 1) b := by
          have ha := rem_add_choose (d + 1) a
          have hb := rem_add_choose (d + 1) b
          rw [ht] at ha; omega
        obtain ⟨i, hi, hlt⟩ := lex_vec_of_lt d hrem
        refine ⟨i + 1, fun j hj => ?_, by simpa only [vec_succ_succ] using hlt⟩
        cases j with
        | zero => simp only [vec_succ_zero, ht]
        | succ j => simpa only [vec_succ_succ] using hi j (by omega)
      · exfalso
        have h1 := lt_choose_top_succ (d + 1) b
        have h2 : (top (d + 1) b + 1).choose (d + 1 + 1) ≤ (top (d + 1) a).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ ht
        have h3 := choose_top_le (d + 1) a
        omega

theorem not_lex_self (x : ℕ → ℕ) : ¬ Pi.Lex (· < ·) (fun {_} => (· < ·)) x x := by
  rintro ⟨i, -, h⟩; exact lt_irrefl _ h

theorem vec_injective (d : ℕ) {a b : ℕ} (h : vec (d + 1) a = vec (d + 1) b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lex_vec_of_lt d hab; rw [h] at this; exact (not_lex_self _ this).elim
  · exact hab
  · have := lex_vec_of_lt d hab; rw [h] at this; exact (not_lex_self _ this).elim

theorem eq_or_lex_of_le (d : ℕ) {a b : ℕ} (h : a ≤ b) :
    vec (d + 1) a = vec (d + 1) b ∨
      Pi.Lex (· < ·) (fun {_} => (· < ·)) (vec (d + 1) a) (vec (d + 1) b) := by
  rcases h.eq_or_lt with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (lex_vec_of_lt d h)

theorem head_le_of_eq_or_lex {x y : ℕ → ℕ}
    (h : x = y ∨ Pi.Lex (· < ·) (fun {_} => (· < ·)) x y) : x 0 ≤ y 0 := by
  rcases h with h | ⟨i, hi, hlt⟩
  · rw [h]
  · cases i with
    | zero => exact hlt.le
    | succ i => exact (hi 0 (by omega)).le

open Classical in
/-- The first index where the sequence falls below the threshold, or zero if there is no such
index. -/
noncomputable def cnt (t : ℕ) (x : ℕ → ℕ) : ℕ :=
  if h : ∃ p, x p < t then Nat.find h else 0

theorem cnt_eq (t : ℕ) (x : ℕ → ℕ) (h : ∃ p, x p < t) : cnt t x = Nat.find h := by
  rw [cnt, dite_eq_left h]

/-- The finite vector of threshold-crossing indices for descending thresholds. -/
noncomputable def cv (M : ℕ) (x : ℕ → ℕ) : Fin M → ℕ := fun i => cnt (M - i) x

theorem cv_lex {M : ℕ} {x y : ℕ → ℕ} (hy : Antitone y) (hyM : y 0 ≤ M) (hy0 : ∃ q, y q = 0)
    (h : Pi.Lex (· < ·) (fun {_} => (· < ·)) x y) :
    Pi.Lex (· < ·) (fun {_} => (· < ·)) (cv M x) (cv M y) := by
  obtain ⟨p, hp, hlt⟩ := h
  set t := y p with ht
  have ht1 : 1 ≤ t := by simp only [ht]; omega
  have htM : t ≤ M := (hy (Nat.zero_le p)).trans hyM
  refine ⟨⟨M - t, by omega⟩, fun j hj => ?_, ?_⟩
  · have hj' : (j : ℕ) < M - t := hj
    set t' := M - (j : ℕ) with ht'
    have htt' : t < t' := by omega
    have hey : ∃ q, y q < t' := ⟨p, by omega⟩
    change cnt t' x = cnt t' y
    rw [cnt_eq t' y hey]
    set c := Nat.find hey with hc
    have hcspec : y c < t' := Nat.find_spec hey
    have hcmin : ∀ q < c, ¬ y q < t' := fun q hq => Nat.find_min hey hq
    have hcp : c ≤ p := Nat.find_min' hey (show y p < t' by omega)
    have hex : ∃ q, x q < t' := ⟨c, by
      rcases hcp.eq_or_lt with h | h
      · rw [h]; omega
      · rw [hp c h]; exact hcspec⟩
    rw [cnt_eq t' x hex, Nat.find_eq_iff]
    refine ⟨?_, fun q hq => ?_⟩
    · rcases hcp.eq_or_lt with h | h
      · rw [h]; omega
      · rw [hp c h]; exact hcspec
    · rw [hp q (by omega)]; exact hcmin q hq
  · change cnt (M - (M - t)) x < cnt (M - (M - t)) y
    have hMt : M - (M - t) = t := by omega
    rw [hMt]
    have hex : ∃ q, x q < t := ⟨p, hlt⟩
    have hey : ∃ q, y q < t := by obtain ⟨q, hq⟩ := hy0; exact ⟨q, by omega⟩
    rw [cnt_eq t x hex, cnt_eq t y hey]
    have h1 : Nat.find hex = p := by
      rw [Nat.find_eq_iff]
      refine ⟨hlt, fun q hq => ?_⟩
      rw [hp q hq]
      have := hy hq.le
      omega
    rw [h1, Nat.lt_find_iff]
    intro q hq
    have := hy hq
    omega

theorem eventually_eq (H : ℕ → ℕ) (d₀ : ℕ)
    (hH : ∀ d, d₀ ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d)) :
    ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e) := by
  set w : ℕ → ℕ → ℕ := fun d => vec d (H d) with hw
  have hstep : ∀ d, d₀ ≤ d →
      w (d + 1) = w d ∨ Pi.Lex (· < ·) (fun {_} => (· < ·)) (w (d + 1)) (w d) := by
    intro d hd
    have h := eq_or_lex_of_le d (hH d hd)
    rw [vec_macaulayPow d (H d)] at h
    exact h
  set M := w d₀ 0 with hM
  have hhead : ∀ d, d₀ ≤ d → w d 0 ≤ M := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => exact le_rfl
    | succ d hd ih => exact (head_le_of_eq_or_lex (hstep d hd)).trans ih
  have wf : WellFounded (Pi.Lex (· < ·) (fun {_ : Fin M} => ((· < ·) : ℕ → ℕ → Prop))) :=
    Pi.Lex.wellFounded (· < ·)
  obtain ⟨_, ⟨n₀, rfl⟩, hmin⟩ :=
    wf.has_min (Set.range fun n : ℕ => cv M (w (d₀ + n))) ⟨_, 0, rfl⟩
  refine ⟨d₀ + n₀, ?_⟩
  have hconst : ∀ d, d₀ + n₀ ≤ d → w d = w (d₀ + n₀) := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => rfl
    | succ d hd ih =>
        rcases hstep d (by omega) with h | h
        · exact h.trans ih
        · exfalso
          rw [ih] at h
          have hlex := cv_lex (M := M) (vec_antitone _ _) (hhead _ (by omega))
            ⟨d₀ + n₀, vec_eq_zero_of_le _ _ _ le_rfl⟩ h
          refine hmin (cv M (w (d + 1))) ⟨d + 1 - d₀, ?_⟩ hlex
          change cv M (w (d₀ + (d + 1 - d₀))) = cv M (w (d + 1))
          rw [show d₀ + (d + 1 - d₀) = d + 1 by omega]
  intro e he
  have h1 : w (e + 1) = w e := (hconst (e + 1) (by omega)).trans (hconst e he).symm
  have h2 : vec (e + 1) (H (e + 1)) = vec (e + 1) (Nat.macaulayPow e (H e)) := by
    rw [vec_macaulayPow e (H e)]; exact h1
  exact vec_injective e h2

end GotzNum

attribute [local simp] GotzNum.vec_zero
attribute [local simp] GotzNum.vec_succ_zero
attribute [local simp] GotzNum.vec_succ_succ


open GotzNum in
theorem _root_.Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
    (H : ℕ → ℕ) (d₀ : ℕ) (_hd₀ : 1 ≤ d₀)
    (hH : ∀ d, d₀ ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d)) :
    ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e) :=
  eventually_eq H d₀ hH
end Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
