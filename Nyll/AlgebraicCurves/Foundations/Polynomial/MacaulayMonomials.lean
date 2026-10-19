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


import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Group.Embedding
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# Monomial exponent sets and dimensions of homogeneous quotients

The degree and support bounds use one family of finite exponent sets.
Coefficient maps identify homogeneous quotient pieces with coordinate spaces.
-/

namespace MvPolynomial.Macaulay

open AlgebraicGeometry.HilbertFunctor

variable (n : ℕ)

/-- The finite set of exponent vectors of the specified total degree. -/
noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

@[scoped simp] theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) : m ∈ Mon n e ↔ m.degree = e := by
  simp only [Mon, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The exponent vectors of the specified degree supported on the first given number of
variables. -/
noncomputable def MonW (w e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  (Mon n e).filter (fun m => ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0)

theorem mem_MonW (w e : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    m ∈ MonW n w e ↔ m.degree = e ∧ ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0 := by
  simp only [MonW, Finset.mem_filter, mem_Mon]

theorem MonW_mono {w w' : ℕ} (h : w ≤ w') (e : ℕ) : MonW n w e ⊆ MonW n w' e := by
  intro m hm
  rw [mem_MonW] at hm ⊢
  exact ⟨hm.1, fun i hi => hm.2 i (h.trans hi)⟩

theorem MonW_of_le {w : ℕ} (h : n + 1 ≤ w) (e : ℕ) : MonW n w e = Mon n e := by
  ext m
  simp only [mem_MonW, mem_Mon, and_iff_left_iff_imp]
  intro _ i hi
  exact absurd (lt_of_lt_of_le i.2 (h.trans hi)) (lt_irrefl _)

/-- The exponent vector of the specified variable. -/
noncomputable def var (j : ℕ) (h : j < n + 1) : Fin (n + 1) →₀ ℕ := Finsupp.single ⟨j, h⟩ 1

@[scoped simp] theorem var_apply (j : ℕ) (h : j < n + 1) (i : Fin (n + 1)) :
    var n j h i = if (i : ℕ) = j then 1 else 0 := by
  simp only [var, Finsupp.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

@[scoped simp] theorem degree_var (j : ℕ) (h : j < n + 1) : (var n j h).degree = 1 := by
  simp only [var, Finsupp.degree_single]

/-- The exponent set shifted by the specified variable, or empty when its index is out of range. -/
noncomputable def shift (j : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  if h : j < n + 1 then B.map (addRightEmbedding (var n j h)) else ∅

theorem shift_of_le {j : ℕ} (h : n + 1 ≤ j) (B : Finset (Fin (n + 1) →₀ ℕ)) : shift n j B = ∅ := by
  simp only [shift, dite_eq_right (not_lt.mpr h)]

theorem mem_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ ∃ b ∈ B, b + var n j h = u := by
  simp only [shift, dite_eq_left h, Finset.mem_map, addRightEmbedding_apply]

theorem card_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    (shift n j B).card = B.card := by
  simp only [shift, dite_eq_left h, Finset.card_map]

@[scoped simp] theorem shift_empty (j : ℕ) : shift n j (∅ : Finset (Fin (n + 1) →₀ ℕ)) = ∅ := by
  unfold shift
  split_ifs <;> simp only [Finset.map_empty]

theorem shift_mono (j : ℕ) {B B' : Finset (Fin (n + 1) →₀ ℕ)} (hB : B ⊆ B') :
    shift n j B ⊆ shift n j B' := by
  unfold shift; split_ifs
  · exact Finset.map_subset_map.mpr hB
  · exact Finset.Subset.refl _

theorem sub_var_add_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    u - var n j h + var n j h = u := by
  unfold var
  exact Finsupp.sub_add_single_one_cancel (by omega)

theorem add_var_sub_var {j : ℕ} (h : j < n + 1) (b : Fin (n + 1) →₀ ℕ) :
    b + var n j h - var n j h = b :=
  add_tsub_cancel_right _ _

theorem mem_shift_iff {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ))
    (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ 1 ≤ u ⟨j, h⟩ ∧ u - var n j h ∈ B := by
  rw [mem_shift n h]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨?_, by simpa only [add_var_sub_var] using hb⟩
    simp only [Finsupp.add_apply, var, Finsupp.single_eq_same]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, sub_var_add_var n h u h1⟩

theorem degree_sub_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    (u - var n j h).degree + 1 = u.degree := by
  conv_rhs => rw [← sub_var_add_var n h u hu]
  rw [map_add, degree_var]

theorem MonW_succ {j : ℕ} (h : j < n + 1) (e : ℕ) :
    MonW n (j + 1) (e + 1) = MonW n j (e + 1) ∪ shift n j (MonW n (j + 1) e) := by
  ext u
  rw [Finset.mem_union, mem_shift_iff n h, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨hdeg, hsupp⟩
    by_cases huj : u ⟨j, h⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, h⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp i hij
    · refine Or.inr ⟨by omega, ?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u (by omega)
        omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
        rw [hsupp i hi, Nat.zero_sub]
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, hdeg, hsupp⟩)
    · exact ⟨hdeg, fun i hi => hsupp i (by omega)⟩
    · refine ⟨?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u h1
        omega
      · have := hsupp i hi
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at this
        have hij : (i : ℕ) ≠ j := by omega
        simpa only [ite_eq_right hij, Nat.sub_zero] using this

theorem disjoint_MonW_shift (j e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    Disjoint (MonW n j e) (shift n j B) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  by_cases h : j < n + 1
  · rw [mem_shift_iff n h] at hu'
    rw [mem_MonW] at hu
    have := hu.2 ⟨j, h⟩ le_rfl
    omega
  · rw [shift_of_le n (not_lt.mp h)] at hu'
    exact Finset.notMem_empty _ hu'

theorem MonW_zero_succ (e : ℕ) : MonW n 0 (e + 1) = ∅ := by
  ext u
  simp only [mem_MonW, Finset.notMem_empty, iff_false, not_and]
  intro hdeg hsupp
  have : u = 0 := by
    ext i; exact hsupp i (Nat.zero_le _)
  rw [this, map_zero] at hdeg
  omega

theorem MonW_zero_right (w : ℕ) : MonW n w 0 = {0} := by
  ext u
  simp only [mem_MonW, Finset.mem_singleton, Finsupp.degree_eq_zero_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, fun _ _ => Finsupp.zero_apply⟩

theorem card_MonW : ∀ (w e : ℕ), w ≤ n + 1 → (MonW n w e).card = (w + e - 1).choose e
  | w, 0, _ => by rw [MonW_zero_right, Finset.card_singleton, Nat.choose_zero_right]
  | 0, e + 1, _ => by
      rw [MonW_zero_succ, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]
  | w + 1, e + 1, hw => by
      rw [MonW_succ n (by omega), Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _),
        card_shift n (by omega), card_MonW w (e + 1) (by omega), card_MonW (w + 1) e hw,
        show w + 1 + (e + 1) - 1 = (w + e) + 1 by omega, Nat.choose_succ_succ',
        show w + (e + 1) - 1 = w + e by omega, show w + 1 + e - 1 = w + e by omega, add_comm]

theorem card_Mon (e : ℕ) : (Mon n e).card = (n + e).choose n := by
  rw [← MonW_of_le n le_rfl, card_MonW n (n + 1) e le_rfl, show n + 1 + e - 1 = n + e by omega,
    Nat.choose_symm_add]

theorem degree_eq_of_mem_support (K : Type) [Field K] {e : ℕ} {p : MvPolynomial (Fin (n + 1)) K}
    (hp : p.IsHomogeneous e) {m : Fin (n + 1) →₀ ℕ} (hm : m ∈ p.support) : m.degree = e := by
  have h : p ∈ homogeneousSubmodule (Fin (n + 1)) K e := hp
  rw [homogeneousSubmodule_eq_finsupp_supported] at h
  exact h hm

theorem finrank_piece_eq_card (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e :
  ℕ)
    (D : Finset (Fin (n + 1) →₀ ℕ)) (hD : ∀ m ∈ D, m.degree = e)
    (hJ : ∀ p : MvPolynomial (Fin (n + 1)) K, p.IsHomogeneous e →
      (p ∈ J ↔ ∀ m ∈ D, p.coeff m = 0)) :
    Module.finrank K (piece J e) = D.card := by
  classical
  set V := homogeneousSubmodule (Fin (n + 1)) K e with hV
  let φ : ↥V →ₗ[K] (↥D → K) :=
    LinearMap.pi fun m => (lcoeff K m.1).comp V.subtype
  have hφ : ∀ (p : ↥V) (m : ↥D), φ p m = p.1.coeff m.1 := fun _ _ => rfl
  have hker : LinearMap.ker φ = Submodule.comap V.subtype (J.restrictScalars K) := by
    ext p
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem,
      Submodule.subtype_apply,
      hJ p.1 p.2, funext_iff]
    constructor
    · intro h m hm; exact h ⟨m, hm⟩
    · intro h m; exact h m.1 m.2
  have hsurj : Function.Surjective φ := by
    intro f
    let q : MvPolynomial (Fin (n + 1)) K := ∑ m : ↥D, f m • monomial m.1 (1 : K)
    have hq : q ∈ V :=
      Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (isHomogeneous_monomial _ (hD m.1 m.2))
    refine ⟨⟨q, hq⟩, funext fun m' => ?_⟩
    rw [hφ]
    simp only [q, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single m']
    · exact ite_eq_left rfl
    · intro m _ hm
      rw [ite_eq_right]
      exact fun h => hm (Subtype.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  have e₁ : piece J e ≃ₗ[K] (↥D → K) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)
  rw [e₁.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

end MvPolynomial.Macaulay
