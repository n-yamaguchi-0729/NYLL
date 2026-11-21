/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.ValuedFieldTheory.Valuation.Subring.Integral.NormalizedPolynomial
public import Nyll.SchemeTheory.RingTheory.Polynomial.MultisetLinearFactorNormalization
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr.Core
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Algebra.Polynomial.Inductions

/-!
# Valuation Subring exists aeval div eq aeval div add aeval inv div
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div

open Polynomial

namespace P1aSol

open ValuationSubring.NormalizedPolynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem valuation_ne_one_of_isRoot {t : L[X]} {d : ℕ} (hd : A.valuation (t.coeff d) = 1)
    (ht : ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) {ρ : L} (hρ : t.IsRoot ρ) :
    A.valuation ρ ≠ 1 := by
  intro h1
  have htd : t.coeff d ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hdle : d ≤ t.natDegree := le_natDegree_of_ne_zero htd
  have hev : t.eval ρ = 0 := hρ
  rw [eval_eq_sum_range] at hev
  have hdmem : d ∈ Finset.range (t.natDegree + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hdle)
  rw [← Finset.add_sum_erase _ _ hdmem] at hev
  have hkey : t.coeff d * ρ ^ d =
      -∑ j ∈ (Finset.range (t.natDegree + 1)).erase d, t.coeff j * ρ ^ j := by
    linear_combination hev
  have hlt : A.valuation (∑ j ∈ (Finset.range (t.natDegree + 1)).erase d, t.coeff j * ρ ^ j)
      < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [map_mul, map_pow, h1, one_pow, mul_one]
    exact ht j hj.1
  have hval : A.valuation (t.coeff d * ρ ^ d) = 1 := by
    rw [map_mul, map_pow, hd, h1, one_pow, one_mul]
  rw [hkey, Valuation.map_neg] at hval
  exact absurd hval (ne_of_lt hlt)

variable [IsAlgClosed L]

theorem exists_eq_C_mul_prod_mul_prod {t : L[X]} {d : ℕ} (hd : A.valuation (t.coeff d) = 1)
    (ht : ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) :
    ∃ (u : L) (sm : Multiset L) (cs : Multiset L),
      u ≠ 0 ∧ 1 ≤ A.valuation u ∧ (∀ ρ ∈ sm, A.valuation ρ < 1) ∧ (∀ c ∈ cs, A.valuation c < 1) ∧
      t = C u * (sm.map fun ρ => (X - C ρ : L[X])).prod *
        (cs.map fun c => (1 - C c * X : L[X])).prod := by
  classical
  have htd : t.coeff d ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have ht0 : t ≠ 0 := fun h => htd (by rw [h, coeff_zero])
  have hsplit : C t.leadingCoeff * (t.roots.map fun a => X - C a).prod = t :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  set sm := t.roots.filter fun ρ => A.valuation ρ < 1 with hsm
  set lg := t.roots.filter fun ρ => ¬ A.valuation ρ < 1 with hlg
  have hsplit2 : t.roots = sm + lg := (Multiset.filter_add_not _ _).symm
  have hlg1 : ∀ ρ ∈ lg, 1 < A.valuation ρ := by
    intro ρ hρ
    rw [hlg, Multiset.mem_filter] at hρ
    have hne := valuation_ne_one_of_isRoot A hd ht ((mem_roots ht0).mp hρ.1)
    exact lt_of_le_of_ne (not_lt.mp hρ.2) (Ne.symm hne)
  have hlg0 : ∀ ρ ∈ lg, ρ ≠ 0 := by
    intro ρ hρ h; have := hlg1 ρ hρ; rw [h, map_zero] at this
    exact absurd this (not_lt.mpr zero_le)
  set u : L := t.leadingCoeff * (lg.map fun ρ => -ρ).prod with hu
  set cs : Multiset L := lg.map fun ρ => ρ⁻¹ with hcs
  have hcs1 : ∀ c ∈ cs, A.valuation c < 1 := by
    intro c hc
    rw [hcs, Multiset.mem_map] at hc
    obtain ⟨ρ, hρ, rfl⟩ := hc
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (hlg1 ρ hρ)
  have hsm1 : ∀ ρ ∈ sm, A.valuation ρ < 1 := by
    intro ρ hρ; rw [hsm, Multiset.mem_filter] at hρ; exact hρ.2
  set P : L[X] := (sm.map fun ρ => (X - C ρ : L[X])).prod *
    (cs.map fun c => (1 - C c * X : L[X])).prod with hP
  have hfac : t = C u * P := by
    conv_lhs => rw [← hsplit, hsplit2, Multiset.map_add, Multiset.prod_add,
      Polynomial.prod_X_sub_C_eq_C_mul_prod_one_sub lg hlg0]
    rw [hP, hu, hcs, C_mul]
    ring
  have hu0 : u ≠ 0 := by
    intro h; apply ht0; rw [hfac, h, C_0, zero_mul]
  have hPA : ACoeff A P := by
    apply ACoeff.mul
    · apply ACoeff.multiset_prod
      intro ρ hρ
      exact ACoeff.sub A (ACoeff.X A) (ACoeff.C A ((A.valuation_le_one_iff _).mp (hsm1 ρ hρ).le))
    · exact (IsGood.multiset_prod_one_sub A cs hcs1).acoeff A
  have hu1 : 1 ≤ A.valuation u := by
    have h1 : t.coeff d = u * P.coeff d := by
      conv_lhs => rw [hfac]
      rw [coeff_C_mul]
    have h2 : A.valuation (t.coeff d) ≤ A.valuation u * 1 := by
      rw [h1, map_mul]
      gcongr
      exact hPA.valuation_le A d
    rw [hd, mul_one] at h2
    exact h2
  exact ⟨u, sm, cs, hu0, hu1, hsm1, hcs1, by rw [hfac, hP, mul_assoc]⟩

section Charts

variable {F : Type*} [Field F] [Algebra L F]

/-- The condition of being a sum of fractions regular in the element and its inverse. -/
def InM (g x : F) : Prop :=
  ∃ y z : F, IsLam A g y ∧ IsLam A g⁻¹ z ∧ x = y + z
omit [IsAlgClosed L] in
theorem aeval_prod_one_sub (g : F) (rs : Multiset L) :
    aeval g ((rs.map fun r => (1 - Polynomial.C r * X : L[X])).prod) =
      (rs.map fun r => 1 - algebraMap L F r * g).prod := by
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp only [Function.comp_apply, map_sub, map_one, map_mul, aeval_C, aeval_X]
omit [IsAlgClosed L] in
theorem isLam_of_mul_prod_eq {g x : F} (rs : Multiset L) (hrs : ∀ r ∈ rs, A.valuation r < 1)
    {q : L[X]} (hq : ACoeff A q)
    (h : x * (rs.map fun r => 1 - algebraMap L F r * g).prod = aeval g q) : IsLam A g x := by
  refine ⟨q, (rs.map fun r => (1 - Polynomial.C r * X : L[X])).prod, hq,
    IsGood.multiset_prod_one_sub A rs hrs, ?_⟩
  rw [aeval_prod_one_sub]
  exact h
omit [IsAlgClosed L] in
theorem inM_symm {g x : F} : InM A g x ↔ InM A g⁻¹ x := by
  constructor
  · rintro ⟨y, z, hy, hz, rfl⟩; exact ⟨z, y, hz, by rwa [inv_inv], add_comm y z⟩
  · rintro ⟨y, z, hy, hz, rfl⟩; exact ⟨z, y, by rwa [inv_inv] at hz, hy, add_comm y z⟩
omit [IsAlgClosed L] in
theorem InM.of_isLam {g x : F} (hx : IsLam A g x) : InM A g x :=
  ⟨x, 0, hx, isLam_zero A _, (add_zero x).symm⟩
omit [IsAlgClosed L] in
theorem InM.of_isLam_inv {g x : F} (hx : IsLam A g⁻¹ x) : InM A g x :=
  ⟨0, x, isLam_zero A _, hx, (zero_add x).symm⟩
omit [IsAlgClosed L] in
theorem inM_zero (g : F) : InM A g 0 := InM.of_isLam A (isLam_zero A g)
omit [IsAlgClosed L] in
theorem InM.add {g x y : F} (hx : InM A g x) (hy : InM A g y) : InM A g (x + y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, rfl⟩ := hy
  exact ⟨a + c, b + d, ha.add A hc, hb.add A hd, by ring⟩
omit [IsAlgClosed L] in
theorem InM.smul {g x : F} (hx : InM A g x) {a : L} (ha : a ∈ A) : InM A g (algebraMap L F a * x)
  := by
  obtain ⟨y, z, hy, hz, rfl⟩ := hx
  exact ⟨_, _, (isLam_algebraMap A g ha).mul A hy, (isLam_algebraMap A g⁻¹ ha).mul A hz, by ring⟩
omit [IsAlgClosed L] in
theorem InM.sum {g : F} {ι : Type*} (s : Finset ι) (x : ι → F) (hx : ∀ i ∈ s, InM A g (x i)) :
    InM A g (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using inM_zero A g
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact (hx a (Finset.mem_insert_self _ _)).add A (ih fun i hi => hx i (Finset.mem_insert_of_mem
      hi))
omit [IsAlgClosed L] in
theorem InM.mul_self {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0) (hx : InM A g x) :
    InM A g (g * x) := by
  obtain ⟨y, z, hy, hz, rfl⟩ := hx
  have hgi : Transcendental L g⁻¹ := fun h => hg (IsAlgebraic.inv_iff.mp h)
  obtain ⟨a, haA, z', hz', hze⟩ := hz.exists_eq_add_mul A hgi
  refine ⟨g * y + algebraMap L F a * g, z', (hy.mul_self A).add A ?_, hz', ?_⟩
  · have := (isLam_algebraMap A g haA).mul_self A
    rwa [mul_comm] at this
  · rw [hze]; field_simp; ring
omit [IsAlgClosed L] in
theorem InM.mul_inv_self {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0) (hx : InM A g x) :
    InM A g (g⁻¹ * x) := by
  have hgi : Transcendental L g⁻¹ := fun h => hg (IsAlgebraic.inv_iff.mp h)
  rw [inM_symm] at hx ⊢
  exact hx.mul_self A hgi (inv_ne_zero hg0)
omit [IsAlgClosed L] in
theorem InM.mul_pow {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0) (hx : InM A g x) (n : ℕ) :
    InM A g (g ^ n * x) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hx
  | succ n ih => rw [pow_succ, mul_comm (g ^ n) g, mul_assoc]; exact ih.mul_self A hg hg0
omit [IsAlgClosed L] in
theorem InM.mul_inv_pow {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0) (hx : InM A g x) (n : ℕ) :
    InM A g (g⁻¹ ^ n * x) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hx
  | succ n ih => rw [pow_succ, mul_comm (g⁻¹ ^ n) g⁻¹, mul_assoc]; exact ih.mul_inv_self A hg hg0
omit [IsAlgClosed L] in
theorem InM.mul_aeval {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0) (hx : InM A g x)
    {p : L[X]} (hp : ACoeff A p) : InM A g (aeval g p * x) := by
  rw [aeval_eq_sum_range, Finset.sum_mul]
  refine InM.sum A _ _ fun j _ => ?_
  rw [Algebra.smul_def, mul_assoc]
  exact (hx.mul_pow A hg hg0 j).smul A (hp j)
omit [IsAlgClosed L] in
theorem exists_inM_mul_one_sub_eq_inv_pow {g : F} (hg : Transcendental L g) (hg0 : g ≠ 0)
    {c : L} (hc : A.valuation c < 1) (j : ℕ) :
    ∃ w, InM A g w ∧ w * (1 - algebraMap L F c * g) = g⁻¹ ^ j := by
  induction j with
  | zero =>
    obtain ⟨w, hw, hwe⟩ := (isLam_one A g).exists_mul_one_sub_eq A hg hc
    exact ⟨w, InM.of_isLam A hw, by rw [hwe, pow_zero]⟩
  | succ j ih =>
    obtain ⟨w, hw, hwe⟩ := ih
    refine ⟨g⁻¹ * w, hw.mul_inv_self A hg hg0, ?_⟩
    rw [mul_assoc, hwe, pow_succ, mul_comm]
omit [IsAlgClosed L] in
theorem exists_inM_mul_one_sub_eq_of_fac {g : F} (hg : Transcendental L g) (hg0 : g ≠ 0)
    {c : L} (hc : A.valuation c < 1) (rs : Multiset L) :
    ∀ (z : F) (q : L[X]), (∀ r ∈ rs, A.valuation r < 1) → ACoeff A q →
      z * (rs.map fun r => 1 - algebraMap L F r * g⁻¹).prod = aeval g⁻¹ q →
      ∃ z'', InM A g z'' ∧ z'' * (1 - algebraMap L F c * g) = z := by
  induction rs using Multiset.induction_on with
  | empty =>
    intro z q _ hq h
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one] at h
    choose w hw hwe using fun j => exists_inM_mul_one_sub_eq_inv_pow A hg hg0 hc j
    refine ⟨∑ j ∈ Finset.range (q.natDegree + 1), algebraMap L F (q.coeff j) * w j,
      InM.sum A _ _ fun j _ => (hw j).smul A (hq j), ?_⟩
    rw [h, aeval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, hwe, Algebra.smul_def]
  | cons r rs ih =>
    intro z q hrs hq h
    have hr : A.valuation r < 1 := hrs r (Multiset.mem_cons_self _ _)
    have hrs' : ∀ r' ∈ rs, A.valuation r' < 1 := fun r' hr' => hrs r' (Multiset.mem_cons_of_mem hr')
    have hzL : IsLam A g⁻¹ z := isLam_of_mul_prod_eq A (r ::ₘ rs) hrs hq h
    obtain ⟨z₁, hz₁⟩ : ∃ z₁ : F, z₁ = z * (1 - algebraMap L F r * g⁻¹) := ⟨_, rfl⟩
    have hz₁e : z₁ * (rs.map fun r => 1 - algebraMap L F r * g⁻¹).prod = aeval g⁻¹ q := by
      rw [← h, Multiset.map_cons, Multiset.prod_cons, hz₁]
      ring
    obtain ⟨z₁'', hz₁'', hz₁''e⟩ := ih z₁ q hrs' hq hz₁e
    have hrc : A.valuation (r * c) < 1 := by
      rw [map_mul]
      calc A.valuation r * A.valuation c ≤ 1 * A.valuation c := mul_le_mul_left hr.le _
        _ < 1 := by rw [one_mul]; exact hc
    have h1rc : A.valuation (1 - r * c) = 1 := Valuation.map_one_sub_of_lt _ hrc
    have h1rc0 : (1 - r * c) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1rc; exact zero_ne_one h1rc
    set Q : L := (1 - r * c)⁻¹ with hQ
    have hQA : Q ∈ A := by
      rw [← A.valuation_le_one_iff, hQ, map_inv₀, h1rc, inv_one]
    have hrQA : r * Q ∈ A := by
      rw [← A.valuation_le_one_iff, map_mul]
      calc A.valuation r * A.valuation Q ≤ 1 * 1 :=
            mul_le_mul' hr.le ((A.valuation_le_one_iff _).mpr hQA)
        _ = 1 := one_mul 1
    have hQe : algebraMap L F Q * (1 - algebraMap L F r * algebraMap L F c) = 1 := by
      rw [← map_mul, ← map_one (algebraMap L F), ← map_sub, ← map_mul, hQ,
        inv_mul_cancel₀ h1rc0]
    have hginv : g⁻¹ * g = 1 := inv_mul_cancel₀ hg0
    refine ⟨algebraMap L F Q * z₁'' + algebraMap L F (r * Q) * (g⁻¹ * z),
      (hz₁''.smul A hQA).add A ((InM.of_isLam_inv A (hzL.mul_self A)).smul A hrQA), ?_⟩
    rw [map_mul]
    rw [hz₁] at hz₁''e
    linear_combination (algebraMap L F Q) * hz₁''e
      - (algebraMap L F r * algebraMap L F Q * algebraMap L F c * z) * hginv + z * hQe

theorem InM.exists_mul_one_sub_eq {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0)
    (hx : InM A g x) {c : L} (hc : A.valuation c < 1) :
    ∃ x', InM A g x' ∧ x' * (1 - algebraMap L F c * g) = x := by
  obtain ⟨y, z, hy, hz, rfl⟩ := hx
  obtain ⟨y', hy', hy'e⟩ := hy.exists_mul_one_sub_eq A hg hc
  obtain ⟨q, s, hq, hs, hze⟩ := hz
  obtain ⟨rs, hrs, hsfac⟩ := hs.exists_eq_C_mul_prod A
  have hs0 := hs.coeff_zero_ne A
  have hs0A : (s.coeff 0)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀, hs.1, inv_one]
  have hzfac : z * (rs.map fun r => 1 - algebraMap L F r * g⁻¹).prod =
      aeval g⁻¹ (Polynomial.C (s.coeff 0)⁻¹ * q) := by
    have h1 : aeval g⁻¹ s = algebraMap L F (s.coeff 0) *
        (rs.map fun r => 1 - algebraMap L F r * g⁻¹).prod := by
      conv_lhs => rw [hsfac]
      rw [map_mul, aeval_C, aeval_prod_one_sub]
    rw [map_mul, aeval_C, ← hze, h1, map_inv₀]
    have hs0F : algebraMap L F (s.coeff 0) ≠ 0 := (_root_.map_ne_zero _).mpr hs0
    rw [← mul_assoc, ← mul_assoc, mul_comm _ z, mul_assoc z, inv_mul_cancel₀ hs0F, mul_one]
  obtain ⟨z'', hz'', hz''e⟩ := exists_inM_mul_one_sub_eq_of_fac A hg hg0 hc rs z _ hrs
    (ACoeff.mul A (ACoeff.C A hs0A) hq) hzfac
  refine ⟨y' + z'', (InM.of_isLam A hy').add A hz'', ?_⟩
  rw [add_mul, hy'e, hz''e]

theorem InM.exists_mul_one_sub_inv_eq {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0)
    (hx : InM A g x) {r : L} (hr : A.valuation r < 1) :
    ∃ x', InM A g x' ∧ x' * (1 - algebraMap L F r * g⁻¹) = x := by
  have hgi : Transcendental L g⁻¹ := fun h => hg (IsAlgebraic.inv_iff.mp h)
  rw [inM_symm] at hx
  obtain ⟨x', hx', hx'e⟩ := hx.exists_mul_one_sub_eq A hgi (inv_ne_zero hg0) hr
  exact ⟨x', (inM_symm A).mpr hx', hx'e⟩

theorem InM.exists_mul_prod_eq {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0)
    (hx : InM A g x) (cs : Multiset L) (hcs : ∀ c ∈ cs, A.valuation c < 1) :
    ∃ x', InM A g x' ∧ x' * (cs.map fun c => 1 - algebraMap L F c * g).prod = x := by
  induction cs using Multiset.induction_on with
  | empty => exact ⟨x, hx, by rw [Multiset.map_zero, Multiset.prod_zero, mul_one]⟩
  | cons c cs ih =>
    obtain ⟨x₁, hx₁, hx₁e⟩ := ih fun c' hc' => hcs c' (Multiset.mem_cons_of_mem hc')
    obtain ⟨x₂, hx₂, hx₂e⟩ := hx₁.exists_mul_one_sub_eq A hg hg0 (hcs c (Multiset.mem_cons_self _
      _))
    refine ⟨x₂, hx₂, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc, hx₂e, hx₁e]

theorem InM.exists_mul_prod_inv_eq {g x : F} (hg : Transcendental L g) (hg0 : g ≠ 0)
    (hx : InM A g x) (rs : Multiset L) (hrs : ∀ r ∈ rs, A.valuation r < 1) :
    ∃ x', InM A g x' ∧ x' * (rs.map fun r => 1 - algebraMap L F r * g⁻¹).prod = x := by
  have hgi : Transcendental L g⁻¹ := fun h => hg (IsAlgebraic.inv_iff.mp h)
  obtain ⟨x', hx', hx'e⟩ :=
    ((inM_symm A).mp hx).exists_mul_prod_eq A hgi (inv_ne_zero hg0) rs hrs
  exact ⟨x', (inM_symm A).mpr hx', hx'e⟩

theorem inM_aeval_div {f : F} (hf : Transcendental L f) {p t : L[X]} (hp : ACoeff A p)
    {d : ℕ} (hd : A.valuation (t.coeff d) = 1) (ht : ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) :
    InM A f (aeval f p / aeval f t) := by
  classical
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  obtain ⟨u, sm, cs, hu0, hu1, hsm, hcs, htfac⟩ := exists_eq_C_mul_prod_mul_prod A hd ht
  set Pp : F := (cs.map fun c => 1 - algebraMap L F c * f).prod with hPp
  set Pm : F := (sm.map fun ρ => 1 - algebraMap L F ρ * f⁻¹).prod with hPm
  set m : ℕ := Multiset.card sm with hm
  have hsm_ev : aeval f ((sm.map fun ρ => (X - Polynomial.C ρ : L[X])).prod) = f ^ m * Pm := by
    rw [map_multiset_prod, Multiset.map_map]
    have : (sm.map ((aeval f : L[X] →ₐ[L] F) ∘ fun ρ => (X - Polynomial.C ρ : L[X]))) =
        sm.map fun ρ => f * (1 - algebraMap L F ρ * f⁻¹) := by
      refine Multiset.map_congr rfl fun ρ _ => ?_
      simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]
      field_simp
    rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hPm]
  have htev : aeval f t = algebraMap L F u * (f ^ m * Pm) * Pp := by
    conv_lhs => rw [htfac]
    rw [map_mul, map_mul, aeval_C, hsm_ev, aeval_prod_one_sub]
  have htne : aeval f t ≠ 0 := by
    intro h0
    have htz : t.coeff d ≠ 0 := by
      intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
    exact htz (by
      have : t = 0 := transcendental_iff_injective.mp hf (by rw [h0, map_zero])
      rw [this, coeff_zero])
  have h1 : InM A f 1 := InM.of_isLam A (isLam_one A f)
  obtain ⟨w₁, hw₁, hw₁e⟩ := h1.exists_mul_prod_eq A hf hf0 cs hcs
  obtain ⟨w₂, hw₂, hw₂e⟩ := hw₁.exists_mul_prod_inv_eq A hf hf0 sm hsm
  have huA : u⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hu1
  have hw₃ : InM A f (aeval f (Polynomial.C u⁻¹ * p) * (f⁻¹ ^ m * w₂)) :=
    (hw₂.mul_inv_pow A hf hf0 m).mul_aeval A hf hf0 (ACoeff.mul A (ACoeff.C A huA) hp)
  have hU : algebraMap L F u⁻¹ * algebraMap L F u = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
  have hF : f⁻¹ ^ m * f ^ m = 1 := by rw [← mul_pow, inv_mul_cancel₀ hf0, one_pow]
  have hkey : aeval f (Polynomial.C u⁻¹ * p) * (f⁻¹ ^ m * w₂) * aeval f t = aeval f p := by
    rw [htev, map_mul, aeval_C, ← hPp] at *
    linear_combination
      (algebraMap L F u⁻¹ * algebraMap L F u * f⁻¹ ^ m * f ^ m * aeval f p * Pp) * hw₂e
      + (algebraMap L F u⁻¹ * algebraMap L F u * f⁻¹ ^ m * f ^ m * aeval f p) * hw₁e
      + (aeval f p * (f⁻¹ ^ m * f ^ m)) * hU + (aeval f p) * hF
  have : aeval f p / aeval f t = aeval f (Polynomial.C u⁻¹ * p) * (f⁻¹ ^ m * w₂) :=
    (eq_div_iff htne).mpr hkey |>.symm
  rw [this]
  exact hw₃

end Charts

end P1aSol

open P1aSol ValuationSubring.NormalizedPolynomial in
theorem _root_.ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ j, p.coeff j ∈ A)
    (ht : ∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) :
    ∃ p₁ t₁ q s : L[X],
      (∀ j, p₁.coeff j ∈ A) ∧ (∀ j, q.coeff j ∈ A) ∧
      (A.valuation (t₁.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t₁.coeff j) < 1) ∧
      (A.valuation (s.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (s.coeff j) < 1) ∧
      aeval f p / aeval f t = aeval f p₁ / aeval f t₁ + aeval f⁻¹ q / aeval f⁻¹ s := by
  obtain ⟨d, hd, ht'⟩ := ht
  have hfi : Transcendental L f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  obtain ⟨y, z, ⟨p₁, t₁, hp₁, ht₁, hye⟩, ⟨q, s, hq, hs, hze⟩, hsum⟩ := inM_aeval_div A hf hp hd ht'
  refine ⟨p₁, t₁, q, s, hp₁, hq, ht₁, hs, ?_⟩
  rw [hsum, eq_div_iff (aeval_ne_zero_of_isGood A hf ht₁) |>.mpr hye,
    eq_div_iff (aeval_ne_zero_of_isGood A hfi hs) |>.mpr hze]
end ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
