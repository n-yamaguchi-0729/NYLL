/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Shared definitions and lemmas from these adapted Anthropic FLT sources:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.Polynomial.MultisetLinearFactorNormalization
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr.Core
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push

/-! # Integral coefficients and normalized polynomials over valuation rings -/

@[expose] public section

open Polynomial

namespace ValuationSubring.NormalizedPolynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- The condition that all coefficients of a polynomial belong to the valuation ring. -/
def ACoeff (p : L[X]) : Prop := ∀ j, p.coeff j ∈ A

theorem ACoeff.zero : ACoeff A (0 : L[X]) := fun j => by
  rw [coeff_zero]
  exact A.zero_mem

theorem ACoeff.one : ACoeff A (1 : L[X]) := fun j => by
  rw [coeff_one]
  split_ifs
  · exact A.one_mem
  · exact A.zero_mem

theorem ACoeff.C {a : L} (ha : a ∈ A) : ACoeff A (C a) := fun j => by
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact A.zero_mem

theorem ACoeff.X : ACoeff A (X : L[X]) := fun j => by
  rw [coeff_X]
  split_ifs
  · exact A.one_mem
  · exact A.zero_mem

theorem ACoeff.add {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p + q) :=
  fun j => by rw [coeff_add]; exact A.toSubring.add_mem (hp j) (hq j)

theorem ACoeff.neg {p : L[X]} (hp : ACoeff A p) : ACoeff A (-p) :=
  fun j => by rw [coeff_neg]; exact A.toSubring.neg_mem (hp j)

theorem ACoeff.sub {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p - q) :=
  fun j => by rw [coeff_sub]; exact sub_mem (hp j) (hq j)

theorem ACoeff.mul {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p * q) := by
  intro j
  rw [coeff_mul]
  refine sum_mem fun x _ => ?_
  exact A.toSubring.mul_mem (hp _) (hq _)

theorem ACoeff.multiset_prod {ι : Type*} (s : Multiset ι) (g : ι → L[X])
    (hg : ∀ i ∈ s, ACoeff A (g i)) : ACoeff A (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using ACoeff.one A
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact ACoeff.mul A (hg a (Multiset.mem_cons_self _ _))
      (ih fun i hi => hg i (Multiset.mem_cons_of_mem hi))

theorem ACoeff.divX {p : L[X]} (hp : ACoeff A p) : ACoeff A (divX p) :=
  fun j => by rw [coeff_divX]; exact hp _

theorem ACoeff.valuation_le {p : L[X]} (hp : ACoeff A p) (j : ℕ) :
    A.valuation (p.coeff j) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (hp j)

theorem acoeff_of_valuation_le {p : L[X]} (hp : ∀ j, A.valuation (p.coeff j) ≤ 1) :
    ACoeff A p := fun j => (A.valuation_le_one_iff _).mp (hp j)

theorem ACoeff.X_pow (n : ℕ) : ACoeff A ((Polynomial.X : L[X]) ^ n) := fun j => by
  rw [coeff_X_pow]
  split_ifs
  · exact A.one_mem
  · exact A.zero_mem

theorem ACoeff.prod {ι : Type*} (s : Finset ι) (g : ι → L[X]) (hg : ∀ i ∈ s, ACoeff A (g i)) :
    ACoeff A (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using ACoeff.one A
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ACoeff.mul A (hg a (Finset.mem_insert_self _ _))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- A polynomial with unit-valued constant coefficient and strictly smaller other coefficients. -/
def IsGood (t : L[X]) : Prop :=
  A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1

theorem IsGood.valuation_le {t : L[X]} (ht : IsGood A t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = 0
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem IsGood.acoeff {t : L[X]} (ht : IsGood A t) : ACoeff A t :=
  acoeff_of_valuation_le A (ht.valuation_le A)

theorem IsGood.coeff_zero_ne {t : L[X]} (ht : IsGood A t) : t.coeff 0 ≠ 0 := by
  intro h
  have hval := ht.1
  rw [h, map_zero] at hval
  exact zero_ne_one hval

theorem IsGood.ne_zero {t : L[X]} (ht : IsGood A t) : t ≠ 0 := fun h =>
  ht.coeff_zero_ne A (by rw [h, coeff_zero])

theorem IsGood.one : IsGood A (1 : L[X]) := by
  refine ⟨by rw [AddMonoidAlgebra.coeff_one_zero, map_one], fun j hj => ?_⟩
  rw [coeff_one, ite_eq_right hj, map_zero]; exact zero_lt_one

theorem IsGood.one_sub {c : L} (hc : A.valuation c < 1) :
    IsGood A (1 - Polynomial.C c * Polynomial.X : L[X]) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coeff_sub, AddMonoidAlgebra.coeff_one_zero, coeff_C_mul, coeff_X_zero,
      mul_zero, sub_zero, map_one]
  · rw [coeff_sub, coeff_one, ite_eq_right hj, coeff_C_mul]
    by_cases h1 : j = 1
    · subst h1
      rw [coeff_X_one, mul_one, zero_sub, Valuation.map_neg]
      exact hc
    · rw [coeff_X_of_ne_one h1, mul_zero, sub_zero, map_zero]; exact zero_lt_one

theorem IsGood.mul {t s : L[X]} (ht : IsGood A t) (hs : IsGood A s) : IsGood A (t * s) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [mul_coeff_zero, map_mul, ht.1, hs.1, one_mul]
  · rw [coeff_mul]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_mul]
    by_cases h1 : x.1 = 0
    · have h2 : x.2 ≠ 0 := by omega
      calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ 1 * A.valuation (s.coeff x.2) := by gcongr; exact ht.valuation_le A _
        _ < 1 := by rw [one_mul]; exact hs.2 _ h2
    · calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ A.valuation (t.coeff x.1) * 1 := by gcongr; exact hs.valuation_le A _
        _ < 1 := by rw [mul_one]; exact ht.2 _ h1

theorem IsGood.multiset_prod_one_sub (rs : Multiset L) (hrs : ∀ r ∈ rs, A.valuation r < 1) :
    IsGood A (rs.map fun r => (1 - Polynomial.C r * Polynomial.X : L[X])).prod := by
  induction rs using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using IsGood.one A
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact IsGood.mul A (IsGood.one_sub A (hrs a (Multiset.mem_cons_self _ _)))
      (ih fun r hr => hrs r (Multiset.mem_cons_of_mem hr))

theorem coeff_zero_multiset_prod_one_sub (rs : Multiset L) :
    ((rs.map fun r => (1 - Polynomial.C r * Polynomial.X : L[X])).prod).coeff 0 = 1 := by
  induction rs using Multiset.induction_on with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, AddMonoidAlgebra.coeff_one_zero]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_coeff_zero, ih, mul_one,
      coeff_sub, AddMonoidAlgebra.coeff_one_zero, coeff_C_mul, coeff_X_zero, mul_zero, sub_zero]

theorem IsGood.valuation_eval_eq_one {t : L[X]} (ht : IsGood A t) {c : L}
    (hc : A.valuation c < 1) : A.valuation (t.eval c) = 1 := by
  rw [eval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [Valuation.map_add_eq_of_lt_right]
  · exact ht.1
  · rw [ht.1]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, map_pow]
    calc A.valuation (t.coeff (j + 1)) * A.valuation c ^ (j + 1)
        ≤ 1 * A.valuation c ^ (j + 1) := by gcongr; exact ht.valuation_le A _
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le hc (Nat.succ_ne_zero j)

theorem IsGood.one_lt_valuation_of_isRoot {t : L[X]} (ht : IsGood A t) {ρ : L}
    (hρ : t.IsRoot ρ) : 1 < A.valuation ρ := by
  by_contra hle
  push Not at hle
  have hev : t.eval ρ = 0 := hρ
  rw [eval_eq_sum_range, Finset.sum_range_succ'] at hev
  simp only [pow_zero, mul_one] at hev
  have h0 : t.coeff 0 = -∑ j ∈ Finset.range t.natDegree, t.coeff (j + 1) * ρ ^ (j + 1) := by
    linear_combination hev
  have hlt : A.valuation (∑ j ∈ Finset.range t.natDegree, t.coeff (j + 1) * ρ ^ (j + 1)) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, map_pow]
    calc A.valuation (t.coeff (j + 1)) * A.valuation ρ ^ (j + 1)
        ≤ A.valuation (t.coeff (j + 1)) * 1 := by
          gcongr
          exact pow_le_one₀ zero_le hle
      _ < 1 := by rw [mul_one]; exact ht.2 (j + 1) (Nat.succ_ne_zero j)
  have h1 := ht.1
  rw [h0, Valuation.map_neg] at h1
  exact absurd h1 (ne_of_lt hlt)

theorem IsGood.coeff_mem {t : L[X]} (ht : IsGood A t) (j : ℕ) : t.coeff j ∈ A :=
  (A.valuation_le_one_iff _).mp (ht.valuation_le A j)

theorem IsGood.exists_eq_C_mul_prod [IsAlgClosed L] {s : L[X]} (hs : IsGood A s) :
    ∃ rs : Multiset L, (∀ r ∈ rs, A.valuation r < 1) ∧
      s = C (s.coeff 0) * (rs.map fun r => (1 - C r * X : L[X])).prod := by
  classical
  have hs0 := hs.ne_zero A
  have hsplit : C s.leadingCoeff * (s.roots.map fun a => X - C a).prod = s :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have hroots : ∀ ρ ∈ s.roots, 1 < A.valuation ρ := fun ρ hρ =>
    hs.one_lt_valuation_of_isRoot A ((mem_roots hs0).mp hρ)
  have hroots0 : ∀ ρ ∈ s.roots, ρ ≠ 0 := by
    intro ρ hρ h
    have hval := hroots ρ hρ
    rw [h, map_zero] at hval
    exact absurd hval (not_lt.mpr zero_le)
  refine ⟨s.roots.map fun ρ => ρ⁻¹, ?_, ?_⟩
  · intro r hr
    rw [Multiset.mem_map] at hr
    obtain ⟨ρ, hρ, rfl⟩ := hr
    have h1 := hroots ρ hρ
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  · set P := ((s.roots.map fun ρ => ρ⁻¹).map fun r => (1 - C r * X : L[X])).prod with hP
    have hfac : s = C (s.leadingCoeff * (s.roots.map fun ρ => -ρ).prod) * P := by
      conv_lhs => rw [← hsplit]
      rw [Polynomial.prod_X_sub_C_eq_C_mul_prod_one_sub s.roots hroots0, ← mul_assoc, ← C_mul]
    have hc0 : s.coeff 0 = s.leadingCoeff * (s.roots.map fun ρ => -ρ).prod := by
      conv_lhs => rw [hfac]
      rw [coeff_C_mul, hP, coeff_zero_multiset_prod_one_sub, mul_one]
    rw [hc0]
    exact hfac

theorem aeval_ne_zero_of_isGood {F : Type*} [Field F] [Algebra L F] {g : F}
    (hg : Transcendental L g) {t : L[X]} (ht : IsGood A t) : aeval g t ≠ 0 := fun h =>
  ht.ne_zero A (transcendental_iff_injective.mp hg (by rw [h, map_zero]))

variable {F : Type*} [Field F] [Algebra L F]

/-- The condition of admitting a polynomial fraction with a good denominator at the given
element. -/
def IsLam (g x : F) : Prop :=
  ∃ p t : L[X], ACoeff A p ∧ IsGood A t ∧ x * aeval g t = aeval g p

theorem isLam_aeval (g : F) {p : L[X]} (hp : ACoeff A p) : IsLam A g (aeval g p) :=
  ⟨p, 1, hp, IsGood.one A, by rw [map_one, mul_one]⟩
theorem isLam_algebraMap (g : F) {a : L} (ha : a ∈ A) : IsLam A g (algebraMap L F a) := by
  have := isLam_aeval A g (ACoeff.C A ha)
  rwa [aeval_C] at this
theorem isLam_zero (g : F) : IsLam A g 0 := by
  have := isLam_aeval A g (ACoeff.zero A)
  rwa [map_zero] at this
theorem isLam_one (g : F) : IsLam A g 1 := by
  have := isLam_aeval A g (ACoeff.one A)
  rwa [map_one] at this
theorem IsLam.add {g x y : F} (hx : IsLam A g x) (hy : IsLam A g y) : IsLam A g (x + y) := by
  obtain ⟨p, t, hp, ht, hxe⟩ := hx
  obtain ⟨q, s, hq, hs, hye⟩ := hy
  refine ⟨p * s + q * t, t * s, ACoeff.add A (ACoeff.mul A hp hs.acoeff) (ACoeff.mul A hq
    ht.acoeff),
    IsGood.mul A ht hs, ?_⟩
  simp only [map_add, map_mul]
  linear_combination (aeval g s) * hxe + (aeval g t) * hye
theorem IsLam.mul {g x y : F} (hx : IsLam A g x) (hy : IsLam A g y) : IsLam A g (x * y) := by
  obtain ⟨p, t, hp, ht, hxe⟩ := hx
  obtain ⟨q, s, hq, hs, hye⟩ := hy
  refine ⟨p * q, t * s, ACoeff.mul A hp hq, IsGood.mul A ht hs, ?_⟩
  simp only [map_mul]
  linear_combination (y * aeval g s) * hxe + (aeval g p) * hye
theorem IsLam.mul_self {g x : F} (hx : IsLam A g x) : IsLam A g (g * x) := by
  obtain ⟨p, t, hp, ht, hxe⟩ := hx
  refine ⟨X * p, t, ACoeff.mul A (ACoeff.X A) hp, ht, ?_⟩
  simp only [map_mul, aeval_X]
  linear_combination g * hxe
theorem IsLam.exists_eq_add_mul {g x : F} (hg : Transcendental L g) (hx : IsLam A g x) :
    ∃ a ∈ A, ∃ x', IsLam A g x' ∧ x = algebraMap L F a + g * x' := by
  obtain ⟨p, t, hp, ht, hxe⟩ := hx
  have ht0 := ht.coeff_zero_ne A
  have hat := aeval_ne_zero_of_isGood A hg ht
  set a : L := p.coeff 0 * (t.coeff 0)⁻¹ with ha
  have haA : a ∈ A := by
    rw [← A.valuation_le_one_iff, ha, map_mul, map_inv₀, ht.1, inv_one, mul_one]
    exact hp.valuation_le A 0
  set p' : L[X] := divX (p - Polynomial.C a * t) with hp'
  have hp'A : ACoeff A p' := ACoeff.divX A (ACoeff.sub A hp (ACoeff.mul A (ACoeff.C A haA)
    ht.acoeff))
  have hzero : (p - Polynomial.C a * t).coeff 0 = 0 := by
    rw [coeff_sub, coeff_C_mul, ha, inv_mul_cancel_right₀ ht0, sub_self]
  have hdecomp : X * p' = p - Polynomial.C a * t := by
    have := X_mul_divX_add (p - Polynomial.C a * t)
    rw [hzero, C_0, add_zero] at this
    exact this
  refine ⟨a, haA, aeval g p' / aeval g t, ⟨p', t, hp'A, ht, div_mul_cancel₀ _ hat⟩, ?_⟩
  have h1 : aeval g (X * p') = aeval g (p - Polynomial.C a * t) := by rw [hdecomp]
  simp only [map_mul, aeval_X, map_sub, aeval_C] at h1
  field_simp
  linear_combination hxe - h1
theorem IsLam.exists_mul_one_sub_eq {g x : F} (hg : Transcendental L g) (hx : IsLam A g x)
    {c : L} (hc : A.valuation c < 1) :
    ∃ x', IsLam A g x' ∧ x' * (1 - algebraMap L F c * g) = x := by
  obtain ⟨p, t, hp, ht, hxe⟩ := hx
  have hgood := IsGood.one_sub A hc
  have hne : (1 - algebraMap L F c * g) ≠ 0 := by
    have := aeval_ne_zero_of_isGood A hg hgood
    simpa only [map_sub, map_one, map_mul, aeval_C, aeval_X] using this
  refine ⟨x / (1 - algebraMap L F c * g), ⟨p, t * (1 - Polynomial.C c * X), hp, IsGood.mul A ht
    hgood, ?_⟩,
    div_mul_cancel₀ _ hne⟩
  simp only [map_mul, map_sub, map_one, aeval_C, aeval_X]
  rw [← hxe]
  field_simp
end ValuationSubring.NormalizedPolynomial
