/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Tactic.Push
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.SchemeTheory.RingTheory.Polynomial.Macaulay
import Nyll.AlgebraicCurves.Foundations.Polynomial.MacaulayMonomials

/-!
# Mv Polynomial exists span monomial finrank piece eq and finrank piece succ eq macaulay Pow
-/

section ProofImplementation

open _root_.Nat.Macaulay _root_.MvPolynomial.Macaulay

namespace AlgebraicCurves.Foundations.Polynomial.Proofs
namespace MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow

namespace LexGrowth

variable (n : ℕ)

theorem degree_sub_single (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hu : 1 ≤ u i) :
    (u - Finsupp.single i 1).degree + 1 = u.degree := by
  conv_rhs => rw [← Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)]
  rw [map_add, Finsupp.degree_single]

theorem exists_one_le_of_degree_ne_zero (u : Fin (n + 1) →₀ ℕ) (hu : u.degree ≠ 0) :
    ∃ i, 1 ≤ u i := by
  rw [Finsupp.degree_eq_sum] at hu
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  exact ⟨i, by omega⟩

theorem exists_sub_single_pos (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hi : 1 ≤ u i)
    (hdeg : 2 ≤ u.degree) : ∃ i', 1 ≤ u i' ∧ 1 ≤ (u - Finsupp.single i' 1 : Fin (n + 1) →₀ ℕ) i :=
      by
  by_cases h2 : 2 ≤ u i
  · refine ⟨i, hi, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
  · have hui : u i = 1 := by omega
    have hsum : u i + ∑ k ∈ Finset.univ.erase i, u k = u.degree := by
      rw [Finsupp.degree_eq_sum]; exact Finset.add_sum_erase _ _ (Finset.mem_univ i)
    have hne : ∑ k ∈ Finset.univ.erase i, u k ≠ 0 := by omega
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    refine ⟨k, by omega, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, ite_eq_right hki]; omega

/-- The exponent set built recursively from Macaulay blocks and shifted remainder sets. -/
noncomputable def BW : ℕ → ℕ → Finset (Fin (n + 1) →₀ ℕ)
  | 0, a => if a = 0 then ∅ else {0}
  | δ + 1, a => MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW δ (rem δ a))

theorem BW_succ (δ a : ℕ) :
    BW n (δ + 1) a = MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW n δ (rem δ a)) := rfl

theorem BW_zero_right : ∀ d : ℕ, BW n d 0 = ∅
  | 0 => by simp only [BW, ite_true]
  | δ + 1 => by
      rw [BW_succ, top_zero_right, rem_zero_right, BW_zero_right δ, Nat.sub_self, MonW_zero_succ,
        shift_empty, Finset.empty_union]

theorem card_MonW_succ_eq (w δ : ℕ) (hw : w ≤ n + 1) :
    (MonW n w (δ + 1)).card = (w + δ).choose (δ + 1) := by
  rw [card_MonW n w (δ + 1) hw, show w + (δ + 1) - 1 = w + δ by omega]

theorem top_sub_add (δ a : ℕ) : top δ a - δ + δ = top δ a := Nat.sub_add_cancel (d_le_top δ a)

theorem top_le_of_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a ≤ w + δ := by
  by_contra h
  push Not at h
  have h1 : (w + δ + 1).choose (δ + 1) ≤ (top δ a).choose (δ + 1) := Nat.choose_le_choose _ h
  have h2 := choose_top_le δ a
  rw [Nat.choose_succ_succ'] at h1
  have h3 : 1 ≤ (w + δ).choose δ := Nat.choose_pos (by omega)
  omega

theorem j_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a - δ ≤ w := by
  have := top_le_of_le w δ a ha; omega

theorem j_lt_of_rem_ne_zero (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) (hr : rem δ a ≠ 0) :
    top δ a - δ < w := by
  have hj := j_le w δ a ha
  rcases hj.lt_or_eq with h | h
  · exact h
  · exfalso
    have htop : top δ a = w + δ := by have := d_le_top δ a; omega
    have := rem_add_choose δ a
    rw [htop] at this
    omega

theorem rem_le_card (δ a : ℕ) (hj : top δ a - δ + 1 ≤ n + 1) :
    rem δ a ≤ (MonW n (top δ a - δ + 1) δ).card := by
  rw [card_MonW n _ _ hj, show top δ a - δ + 1 + δ - 1 = top δ a by have := d_le_top δ a; omega]
  exact (rem_lt δ a).le

theorem BW_subset : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → BW n d a ⊆ MonW n w d
  | 0, w, a, hw, ha => by
      simp only [BW]
      split_ifs
      · exact Finset.empty_subset _
      · rw [MonW_zero_right]
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ]
      have hj := j_le w δ a ha
      refine Finset.union_subset (MonW_mono n hj _) ?_
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty]; exact Finset.empty_subset _
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have ih := BW_subset δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        refine (shift_mono n _ ih).trans ?_
        refine subset_trans ?_ (MonW_mono n (show top δ a - δ + 1 ≤ w by omega) (δ + 1))
        rw [MonW_succ n (show top δ a - δ < n + 1 by omega) δ]
        exact Finset.subset_union_right

theorem card_BW : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → (BW n d a).card = a
  | 0, w, a, hw, ha => by
      rw [MonW_zero_right, Finset.card_singleton] at ha
      simp only [BW]
      split_ifs with h
      · rw [Finset.card_empty, h]
      · rw [Finset.card_singleton]
        omega
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ, Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _)]
      have hj := j_le w δ a ha
      rw [card_MonW_succ_eq n _ δ (hj.trans hw), top_sub_add]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.card_empty]
        have := rem_add_choose δ a; omega
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        rw [card_shift n
          (by omega), card_BW δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]
        have := rem_add_choose δ a; omega

/-- The monomials whose every one-variable predecessor belongs to the given set. -/
noncomputable def Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e + 1)).filter (fun u => ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B)

theorem mem_Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ Bplus n w e B ↔
      u ∈ MonW n w (e + 1) ∧ ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B := by
  simp only [Bplus, Finset.mem_filter]

theorem Bplus_empty (w e : ℕ) : Bplus n w e (∅ : Finset (Fin (n + 1) →₀ ℕ)) = ∅ := by
  ext u
  simp only [mem_Bplus, Finset.notMem_empty, imp_false, not_le, Nat.lt_one_iff, iff_false, not_and,
    not_forall]
  intro hu
  rw [mem_MonW] at hu
  obtain ⟨i, hi⟩ := exists_one_le_of_degree_ne_zero n u (by omega)
  exact ⟨i, by omega⟩

theorem Bplus_MonW (w j δ : ℕ) (hjw : j ≤ w) :
    Bplus n w (δ + 1) (MonW n j (δ + 1)) = MonW n j (δ + 2) := by
  ext u
  rw [mem_Bplus, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩
    refine ⟨hdeg, fun i hi => ?_⟩
    by_contra hui
    obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
    have := ((mem_MonW n _ _ _).1 (hdiv i' hi')).2 i hi
    omega
  · rintro ⟨hdeg, hsupp⟩
    refine ⟨⟨hdeg, fun i hi => hsupp i (hjw.trans hi)⟩, fun i hi => ?_⟩
    rw [mem_MonW]
    refine ⟨by have := degree_sub_single n u i hi; omega, fun k hk => ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]

theorem Bplus_union_shift (w j δ : ℕ) (hj : j < n + 1) (hjw : j + 1 ≤ w)
    (B' : Finset (Fin (n + 1) →₀ ℕ)) (hB' : B' ⊆ MonW n (j + 1) δ) :
    Bplus n w (δ + 1) (MonW n j (δ + 1) ∪ shift n j B') =
      MonW n j (δ + 2) ∪ shift n j (Bplus n (j + 1) δ B') := by
  have hB : MonW n j (δ + 1) ∪ shift n j B' ⊆ MonW n (j + 1) (δ + 1) := by
    refine Finset.union_subset (MonW_mono n (Nat.le_succ j) _) ?_
    rw [MonW_succ n hj δ]
    exact (shift_mono n j hB').trans Finset.subset_union_right
  have hvar : var n j hj = Finsupp.single ⟨j, hj⟩ 1 := rfl
  ext u
  rw [mem_Bplus, Finset.mem_union, mem_shift_iff n hj, mem_Bplus, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩
    have hsupp' : ∀ i : Fin (n + 1), j < (i : ℕ) → u i = 0 := by
      intro i hi
      by_contra hui
      obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
      have := ((mem_MonW n _ _ _).1 (hB (hdiv i' hi'))).2 i (by omega)
      omega
    by_cases huj : u ⟨j, hj⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, hj⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp' i hij
    · refine Or.inr ⟨by omega, ⟨?_, fun i hi => ?_⟩, fun l hl => ?_⟩
      · have := degree_sub_var n hj u (by omega); omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp' i (by omega), Nat.zero_sub]
      · have hul : 1 ≤ u l := by
          have : (u - var n j hj) l ≤ u l := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
          omega
        have hv := hdiv l hul
        rw [Finset.mem_union, mem_shift_iff n hj] at hv
        rcases hv with hv | ⟨-, hv⟩
        · exfalso
          have h0 := ((mem_MonW n _ _ _).1 hv).2 ⟨j, hj⟩ le_rfl
          by_cases hlj : l = ⟨j, hj⟩
          · subst hlj
            simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same, var] at h0 hl
            omega
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, ite_eq_right hlj] at h0
            omega
        · have : u - var n j hj - Finsupp.single l 1 = u - Finsupp.single l 1 - var n j hj := by
            ext k
            simp only [Finsupp.coe_tsub, Pi.sub_apply]
            omega
          rw [this]; exact hv
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, ⟨hdeg, hsupp⟩, hdiv⟩)
    · refine ⟨⟨hdeg, fun i hi => hsupp i (by omega)⟩, fun i hi => ?_⟩
      refine Finset.mem_union_left _ ((mem_MonW n _ _ _).2 ⟨?_, fun k hk => ?_⟩)
      · have := degree_sub_single n u i hi; omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]
    · have hu : u - var n j hj + var n j hj = u := sub_var_add_var n hj u h1
      refine ⟨⟨?_, fun i hi => ?_⟩, fun i hi => ?_⟩
      · have := degree_sub_var n hj u h1; omega
      · have h0 := hsupp i (by omega)
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at h0
        have hij : (i : ℕ) ≠ j := by omega
        simp only [hij, ite_false] at h0
        omega
      · rw [Finset.mem_union, mem_shift_iff n hj]
        by_cases hij : i = ⟨j, hj⟩
        · subst hij
          rw [← hvar]
          by_cases hujj : (u - var n j hj) ⟨j, hj⟩ = 0
          · left
            rw [mem_MonW]
            refine ⟨hdeg, fun k hk => ?_⟩
            rcases hk.eq_or_lt with hkj | hkj
            · have : k = ⟨j, hj⟩ := Fin.ext hkj.symm
              rw [this]; exact hujj
            · exact hsupp k hkj
          · right
            have := hdiv ⟨j, hj⟩ (by omega)
            rw [← hvar] at this
            refine ⟨?_, this⟩
            simp only [Finsupp.coe_tsub, Pi.sub_apply] at hujj ⊢
            omega
        · right
          have hii : 1 ≤ (u - var n j hj) i := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
            have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
            simp only [this, ite_false]; omega
          have hv := hdiv i hii
          refine ⟨?_, ?_⟩
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, ite_eq_right hij];
              omega
          · have : u - Finsupp.single i 1 - var n j hj = u - var n j hj - Finsupp.single i 1 := by
              ext k
              simp only [Finsupp.coe_tsub, Pi.sub_apply]
              omega
            rw [this]; exact hv

theorem card_Bplus_BW : ∀ (δ w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w (δ + 1)).card →
    (Bplus n w (δ + 1) (BW n (δ + 1) a)).card = Nat.macaulayPow (δ + 1) a := by
  intro δ
  induction δ with
  | zero =>
      intro w a hw ha
      rw [card_MonW_succ_eq n w 0 hw] at ha
      have hj := j_le w 0 a ha
      rw [BW_succ, rem_zero_left, BW_zero_right, shift_empty, Finset.union_empty,
        Bplus_MonW n w _ 0 hj, card_MonW n _ _ (hj.trans hw), macaulayPow_succ, macaulayPow_zero,
        Nat.sub_zero, show top 0 a + (0 + 2) - 1 = top 0 a + 1 by omega]
      rw [add_zero]
  | succ δ' ih =>
      intro w a hw ha
      set δ := δ' + 1 with hδ
      rw [card_MonW_succ_eq n w δ hw] at ha
      have hj := j_le w δ a ha
      rw [BW_succ, macaulayPow_succ]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.union_empty, Bplus_MonW n w _ δ hj,
          card_MonW n _ _ (hj.trans hw), macaulayPow_zero_right,
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega]
        rw [add_zero]
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hjn : top δ a - δ < n + 1 := by omega
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have hB' := BW_subset n δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        rw [Bplus_union_shift n w _ δ hjn (by omega) _ hB',
          Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _), card_shift n hjn,
          card_MonW n _ _ (hj.trans hw),
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega,
          ih (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]

theorem eq_of_le_of_degree_eq (g m : Fin (n + 1) →₀ ℕ) (h : g ≤ m) (hd : g.degree = m.degree) :
    g = m := by
  have h1 : g + (m - g) = m := add_tsub_cancel_of_le h
  have h2 : (m - g).degree = 0 := by
    have := congrArg Finsupp.degree h1
    rw [map_add] at this; omega
  rw [Finsupp.degree_eq_zero_iff] at h2
  rw [h2, add_zero] at h1
  exact h1

theorem exists_eq_sub_single (g u : Fin (n + 1) →₀ ℕ) (h : g ≤ u) (hd : g.degree + 1 = u.degree) :
    ∃ i, 1 ≤ u i ∧ g = u - Finsupp.single i 1 := by
  have h1 : g + (u - g) = u := add_tsub_cancel_of_le h
  have h2 : (u - g).degree = 1 := by
    have := congrArg Finsupp.degree h1
    rw [map_add] at this; omega
  obtain ⟨i, hi⟩ := exists_one_le_of_degree_ne_zero n (u - g) (by omega)
  have h3 : (u - g - Finsupp.single i 1).degree = 0 := by
    have := degree_sub_single n (u - g) i hi; omega
  rw [Finsupp.degree_eq_zero_iff] at h3
  have h4 : u - g = Finsupp.single i 1 := by
    have := Finsupp.sub_add_single_one_cancel (u := u - g) (i := i) (by omega)
    rw [h3, zero_add] at this
    exact this.symm
  refine ⟨i, ?_, ?_⟩
  · have : (u - g) i ≤ u i := by simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
    omega
  · rw [← h4]
    exact (tsub_tsub_cancel_of_le h).symm

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem exists_ideal (δ a : ℕ) (ha : a ≤ (n + (δ + 1)).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous (δ + 1)) ∧ J =
        Ideal.span s) ∧
      Module.finrank K (piece J (δ + 1)) = a ∧
      Module.finrank K (piece J (δ + 1 + 1)) = Nat.macaulayPow (δ + 1) a := by
  classical
  have hcardMon : (MonW n (n + 1) (δ + 1)).card = (n + (δ + 1)).choose n := by
    rw [MonW_of_le n le_rfl, card_Mon]
  have ha' : a ≤ (MonW n (n + 1) (δ + 1)).card := hcardMon ▸ ha
  set B := BW n (δ + 1) a with hBdef
  have hB : B ⊆ MonW n (n + 1) (δ + 1) := BW_subset n (δ + 1) (n + 1) a le_rfl ha'
  have hBcard : B.card = a := card_BW n (δ + 1) (n + 1) a le_rfl ha'
  have hBplus : (Bplus n (n + 1) (δ + 1) B).card = Nat.macaulayPow (δ + 1) a :=
    card_Bplus_BW n δ (n + 1) a le_rfl ha'
  have hmemB : ∀ m ∈ B, m.degree = δ + 1 := fun m hm => ((mem_MonW n _ _ _).1 (hB hm)).1
  set G : Finset (Fin (n + 1) →₀ ℕ) := Mon n (δ + 1) \ B with hGdef
  have hmemG : ∀ m : Fin (n + 1) →₀ ℕ, m ∈ G ↔ m.degree = δ + 1 ∧ m ∉ B := fun m => by
    simp only [hGdef, Finset.mem_sdiff, mem_Mon]
  set s : Set (MvPolynomial (Fin (n + 1)) K) := (fun m => monomial m (1 : K)) '' (↑G : Set _) with
    hsdef
  refine ⟨Ideal.span s, ⟨s, ?_, rfl⟩, ?_, ?_⟩
  · rintro p ⟨m, hm, rfl⟩
    exact isHomogeneous_monomial _ ((hmemG m).1 hm).1
  · rw [← hBcard]
    refine finrank_piece_eq_card n K _ _ B hmemB fun p hp => ?_
    rw [hsdef, mem_ideal_span_monomial_image]
    constructor
    · intro h m hmB
      by_contra hc
      obtain ⟨g, hg, hgm⟩ := h m (mem_support_iff.mpr hc)
      have hg' := (hmemG g).1 hg
      have : g = m := eq_of_le_of_degree_eq n g m hgm (by rw [hg'.1, hmemB m hmB])
      exact hg'.2 (this ▸ hmB)
    · intro h m hm
      refine ⟨m, (hmemG m).2 ⟨degree_eq_of_mem_support n K hp hm, fun hmB => ?_⟩, le_rfl⟩
      exact (mem_support_iff.1 hm) (h m hmB)
  · rw [← hBplus]
    refine finrank_piece_eq_card n K _ _ (Bplus n (n + 1) (δ + 1) B) (fun u hu => ?_) fun p hp => ?_
    · exact ((mem_MonW n _ _ _).1 ((mem_Bplus n _ _ _ _).1 hu).1).1
    · rw [hsdef, mem_ideal_span_monomial_image]
      constructor
      · intro h u hu
        by_contra hc
        obtain ⟨g, hg, hgu⟩ := h u (mem_support_iff.mpr hc)
        have hg' := (hmemG g).1 hg
        have hu' := (mem_Bplus n _ _ _ _).1 hu
        have hdeg : g.degree + 1 = u.degree := by
          rw [hg'.1, ((mem_MonW n _ _ _).1 hu'.1).1]
        obtain ⟨i, hi, rfl⟩ := exists_eq_sub_single n g u hgu hdeg
        exact hg'.2 (hu'.2 i hi)
      · intro h u hu
        have hdeg : u.degree = δ + 1 + 1 := degree_eq_of_mem_support n K hp hu
        have hnot : u ∉ Bplus n (n + 1) (δ + 1) B := fun hb => (mem_support_iff.1 hu) (h u hb)
        rw [mem_Bplus, mem_MonW] at hnot
        simp only [not_and, not_forall] at hnot
        obtain ⟨i, hi, hiB⟩ := hnot ⟨hdeg, fun i hi => absurd (lt_of_lt_of_le i.2 hi) (lt_irrefl _)⟩
        refine ⟨u - Finsupp.single i 1, (hmemG _).2 ⟨?_, hiB⟩, tsub_le_self⟩
        have := degree_sub_single n u i hi; omega

end LexGrowth

attribute [local simp] MvPolynomial.Macaulay.mem_Mon
attribute [local simp] MvPolynomial.Macaulay.var_apply
attribute [local simp] MvPolynomial.Macaulay.degree_var
attribute [local simp] MvPolynomial.Macaulay.shift_empty


open LexGrowth AlgebraicGeometry.HilbertFunctor in
theorem
  _root_.MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (a : ℕ) (ha : a ≤ (n + d).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J d) = a ∧ Module.finrank K (piece J (d + 1)) = Nat.macaulayPow d a
        := by
  obtain ⟨δ, rfl⟩ : ∃ δ, d = δ + 1 := ⟨d - 1, by omega⟩
  exact exists_ideal n δ a ha K
end MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
end AlgebraicCurves.Foundations.Polynomial.Proofs
end ProofImplementation
