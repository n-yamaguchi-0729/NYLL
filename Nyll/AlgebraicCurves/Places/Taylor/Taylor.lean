/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_PlaceTaylorCoeff.lean
Shared residue and Taylor calculations adapted from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_algebraMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring.lean
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorRem_add.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorRem_smul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_add.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_ord_ne_zero.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_smul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_mul.lean

Source-file correspondence is unconfirmed for:
Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
Place_taylorRem_succ_eq_taylorRem_taylorRem_one
Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero
Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
-/

import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Places.Basic

/-!
# Taylor
-/

section

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

/-- The iterated Taylor remainder obtained by subtracting the value at the place and dividing by
`t`. -/
def taylorRem (v : Place K F) (t f : F) : ℕ → F
  | 0 => f
  | r + 1 => (taylorRem v t f r - algebraMap K F (v.evalAt (taylorRem v t f r))) * t⁻¹

/-- The coefficient of order `r`, obtained by evaluating the iterated Taylor remainder. -/
def taylorCoeff (v : Place K F) (t : F) (r : ℕ) (f : F) : K :=
  v.evalAt (taylorRem v t f r)

variable (v : Place K F) (t f : F)

@[simp]
theorem taylorRem_zero : taylorRem v t f 0 = f := rfl

theorem taylorRem_succ (r : ℕ) :
    taylorRem v t f (r + 1)
      = (taylorRem v t f r - algebraMap K F (v.evalAt (taylorRem v t f r))) * t⁻¹ := rfl
@[simp]
theorem taylorCoeff_zero : taylorCoeff v t 0 f = v.evalAt f := rfl

theorem taylorCoeff_eq (r : ℕ) : taylorCoeff v t r f = v.evalAt (taylorRem v t f r) := rfl

theorem taylorRem_succ' (r : ℕ) :
    taylorRem v t f (r + 1)
      = (taylorRem v t f r - algebraMap K F (taylorCoeff v t r f)) * t⁻¹ := rfl

theorem taylorRem_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorRem v t 0 r = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [taylorRem_succ, ih, ← map_zero (algebraMap K F), v.evalAt_algebraMap, map_zero,
      sub_self, zero_mul]

theorem taylorCoeff_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorCoeff v t r 0 = 0 := by
  rw [taylorCoeff_eq, taylorRem_zero_fun, ← map_zero (algebraMap K F), v.evalAt_algebraMap]

theorem taylorRem_algebraMap_one (v : Place K F) (t : F) (c : K) :
    taylorRem v t (algebraMap K F c) 1 = 0 := by
  change (taylorRem v t (algebraMap K F c) 0 - _) * t⁻¹ = 0
  rw [taylorRem_zero, v.evalAt_algebraMap, sub_self, zero_mul]

theorem taylorRem_eq_add_mul_succ {t : F} (ht : t ≠ 0) (f : F) (r : ℕ) :
    taylorRem v t f r
      = algebraMap K F (taylorCoeff v t r f) + t * taylorRem v t f (r + 1) := by
  rw [taylorRem_succ', mul_comm _ t⁻¹, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  abel

theorem eq_sum_taylorCoeff_mul_pow_add_pow_mul_taylorRem {t : F} (ht : t ≠ 0) (f : F) (n : ℕ) :
    f = (∑ q ∈ Finset.range n, algebraMap K F (taylorCoeff v t q f) * t ^ q)
        + t ^ n * taylorRem v t f n := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, taylorRem_zero, one_mul,
        zero_add]
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nth_rewrite 1 [ih]
    rw [taylorRem_eq_add_mul_succ v ht f n]
    ring

end Place

/-- The matrix of the prescribed Taylor coefficients of the functions at the given places. -/
def jetMatrix {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (f : Fin M → F) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (f j)

theorem jetMatrix_apply {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (f : Fin M → F) (i j : Fin M) :
    jetMatrix P t e f i j = (P i).taylorCoeff (t i) (e i) (f j) := rfl
@[simp]
theorem jetMatrix_order_zero {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F)
    (f : Fin M → F) :
    jetMatrix P t (fun _ => 0) f = Matrix.of fun i j => (P i).evalAt (f j) := rfl

open Classical in
/-- The number of indices at which the given list of places equals `v`. -/
def jetMult {M : ℕ} (P : Fin M → Place K F) (v : Place K F) : ℕ :=
  (Finset.univ.filter fun i => P i = v).card

/-- The effective divisor counting the occurrences of the given places. -/
def jetDivisor {M : ℕ} (P : Fin M → Place K F) : Divisor K F :=
  ∑ i, Finsupp.single (P i) 1

theorem jetDivisor_apply {M : ℕ} (P : Fin M → Place K F) (v : Place K F) :
    jetDivisor P v = (jetMult P v : ℤ) := by
  classical
  simp only [jetDivisor, jetMult, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_boole]

/-- A pattern with a common parameter at equal places and distinct orders below their
multiplicity. -/
def IsConfluentPattern {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ) :
    Prop :=
  (∀ i i', P i = P i' → t i = t i') ∧
  (∀ i i', P i = P i' → e i = e i' → i = i') ∧
  (∀ i, e i < jetMult P (P i))

end AlgebraicCurve

end

end

section

/-!
# Place taylor Rem eq mul inv pow of forall taylor Coeff eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorRem v t f e = f * t⁻¹ ^ e := by
  induction e with
  | zero => rw [taylorRem_zero, pow_zero, mul_one]
  | succ e ih =>
    rw [taylorRem_succ', h e (Nat.lt_succ_self e), map_zero, sub_zero,
      ih (fun q hq => h q (Nat.lt_succ_of_lt hq)), pow_succ, mul_assoc]
end AlgebraicCurves.Places.Proofs.Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
end ProofImplementation

end

section

/-!
# Place taylor Rem mem to Valuation Subring
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_mem_toValuationSubring

open AlgebraicCurve AlgebraicCurve.Place

namespace ProofAuxJetT1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem sub_evalAt_mul_inv_mem' (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    (g - algebraMap K F (v.evalAt g)) * t⁻¹ ∈ v.toValuationSubring := by
  have hc : algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hx : g - algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := sub_mem hg hc
  by_cases hx0 : g - algebraMap K F (v.evalAt g) = 0
  · rw [hx0, zero_mul]; exact zero_mem _
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at ht
    exact zero_ne_one ht
  have hval : v.evalAt (g - algebraMap K F (v.evalAt g)) = 0 := by
    rw [v.evalAt_sub_of_mem hv hg hc, v.evalAt_algebraMap, sub_self]
  have hord0 : v.ord (g - algebraMap K F (v.evalAt g)) ≠ 0 := fun h0 =>
    v.evalAt_ne_zero hv hx0 h0 hval
  have hord1 : 1 ≤ v.ord (g - algebraMap K F (v.evalAt g)) := by
    have := v.ord_nonneg_of_mem hx; omega
  apply v.mem_of_ord_nonneg (mul_ne_zero hx0 (inv_ne_zero ht0))
  rw [v.ord_mul hx0 (inv_ne_zero ht0), v.ord_inv, ht]
  omega

end ProofAuxJetT1

theorem _root_.AlgebraicCurve.Place.taylorRem_mem_toValuationSubring
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (r : ℕ) :
    taylorRem v t f r ∈ v.toValuationSubring := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    rw [taylorRem_succ]
    exact ProofAuxJetT1.sub_evalAt_mul_inv_mem' v hv ht ih
end AlgebraicCurves.Places.Proofs.Place_taylorRem_mem_toValuationSubring
end ProofImplementation

end

section

/-!
# Place taylor Rem succ eq taylor Rem taylor Rem one
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_succ_eq_taylorRem_taylorRem_one

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorRem_succ_eq_taylorRem_taylorRem_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorRem v t f (r + 1) = taylorRem v t (taylorRem v t f 1) r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [taylorRem_succ, ih, ← taylorRem_succ]
end AlgebraicCurves.Places.Proofs.Place_taylorRem_succ_eq_taylorRem_taylorRem_one
end ProofImplementation

end

section

/-!
# Place forall lt taylor Coeff eq zero iff le ord
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord

open AlgebraicCurve AlgebraicCurve.Place

namespace ProofAuxJetT2
open AlgebraicCurve AlgebraicCurve.Place IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_mul_inv_pow (v : Place K F) {t f : F} (ht0 : t ≠ 0) (hf0 : f ≠ 0) (ht : v.ord t = 1)
    (q : ℕ) : v.ord (f * t⁻¹ ^ q) = v.ord f - q := by
  have hq0 : t⁻¹ ^ q ≠ 0 := pow_ne_zero _ (inv_ne_zero ht0)
  rw [v.ord_mul hf0 hq0, ← zpow_natCast, v.ord_zpow, v.ord_inv, ht]
  ring

end ProofAuxJetT2

open ProofAuxJetT2 in
theorem _root_.AlgebraicCurve.Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (e : ℕ) :
    (∀ q, q < e → taylorCoeff v t q f = 0) ↔ (e : ℤ) ≤ v.ord f := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at ht
    exact zero_ne_one ht
  have hford : 0 ≤ v.ord f := v.ord_nonneg_of_mem hf
  induction e with
  | zero =>
      constructor
      · intro _
        exact hford
      · intro _ q hq
        exact (Nat.not_lt_zero q hq).elim
  | succ e ih =>
    constructor
    · intro h
      have hlow : ∀ q, q < e → taylorCoeff v t q f = 0 := fun q hq => h q (Nat.lt_succ_of_lt hq)
      have he : (e : ℤ) ≤ v.ord f := ih.mp hlow
      have hrem : taylorRem v t f e = f * t⁻¹ ^ e :=
        taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero v t f hlow
      have hval : v.evalAt (f * t⁻¹ ^ e) = 0 := by
        rw [← hrem, ← taylorCoeff_eq]; exact h e (Nat.lt_succ_self e)
      have hne : f * t⁻¹ ^ e ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ (inv_ne_zero ht0))
      have hord : v.ord (f * t⁻¹ ^ e) ≠ 0 := fun h0 =>
        v.evalAt_ne_zero hv hne h0 hval
      have := ord_mul_inv_pow v ht0 hf0 ht e
      push_cast
      omega
    · intro h q hq
      have hlow : ∀ p, p < e → taylorCoeff v t p f = 0 := ih.mpr (by push_cast at h; omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
      · exact hlow q hq'
      · rw [taylorCoeff_eq, taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero v t f hlow]
        apply evalAt_eq_zero_of_ord_pos v (mul_ne_zero hf0 (pow_ne_zero _ (inv_ne_zero ht0)))
        rw [ord_mul_inv_pow v ht0 hf0 ht]
        push_cast at h
        omega
end AlgebraicCurves.Places.Proofs.Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord
end ProofImplementation

end

section

/-!
# Place taylor Coeff eq eval At mul inv pow of forall taylor Coeff eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorCoeff v t e f = v.evalAt (f * t⁻¹ ^ e) := by
  rw [taylorCoeff_eq, taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero v t f h]
end Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero
end AlgebraicCurves.Places.Proofs
end ProofImplementation

end

section

/-!
# Place taylor Coeff succ eq taylor Coeff taylor Rem one
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorCoeff v t (r + 1) f = taylorCoeff v t r (taylorRem v t f 1) := by
  rw [taylorCoeff_eq, taylorCoeff_eq, taylorRem_succ_eq_taylorRem_taylorRem_one]
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
end ProofImplementation

end

section

/-!
# Place taylor Rem add
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_add

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorRem_add
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorRem v t (f + g) r = taylorRem v t f r + taylorRem v t g r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hfr := taylorRem_mem_toValuationSubring v hv ht hf r
    have hgr := taylorRem_mem_toValuationSubring v hv ht hg r
    rw [taylorRem_succ, taylorRem_succ, taylorRem_succ, ih, v.evalAt_add_of_mem hv hfr hgr, map_add]
    ring
end AlgebraicCurves.Places.Proofs.Place_taylorRem_add
end ProofImplementation

end

section

/-!
# Place taylor Rem smul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_smul

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorRem_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) (r : ℕ) :
    taylorRem v t (c • f) r = c • taylorRem v t f r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hfr := taylorRem_mem_toValuationSubring v hv ht hf r
    rw [taylorRem_succ, taylorRem_succ, ih, v.evalAt_smul_of_mem hv c hfr, map_mul,
      Algebra.smul_def, Algebra.smul_def]
    ring
end AlgebraicCurves.Places.Proofs.Place_taylorRem_smul
end ProofImplementation

end

section

/-!
# Place taylor Coeff add
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_add

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorCoeff_add
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorCoeff v t r (f + g) = taylorCoeff v t r f + taylorCoeff v t r g := by
  rw [taylorCoeff_eq, taylorCoeff_eq, taylorCoeff_eq, taylorRem_add v hv ht hf hg r]
  exact v.evalAt_add_of_mem hv (taylorRem_mem_toValuationSubring v hv ht hf r)
    (taylorRem_mem_toValuationSubring v hv ht hg r)
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_add
end ProofImplementation

end

section

/-!
# Place taylor Coeff algebra Map
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_algebraMap

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem _root_.AlgebraicCurve.Place.taylorCoeff_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t : F) (c : K) (n : ℕ) :
    taylorCoeff v t n (algebraMap K F c) = if n = 0 then c else 0 := by
  rcases n with _ | n
  · rw [ite_eq_left rfl, taylorCoeff_zero, v.evalAt_algebraMap]
  · rw [ite_eq_right (Nat.succ_ne_zero n), taylorCoeff_succ_eq_taylorCoeff_taylorRem_one,
      taylorRem_algebraMap_one, taylorCoeff_zero_fun]
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_algebraMap
end ProofImplementation

end

section

/-!
# Place taylor Coeff ord ne zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_ord_ne_zero

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorCoeff_ord_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    taylorCoeff v t (v.ord f).toNat f ≠ 0 := by
  have hford : 0 ≤ v.ord f := v.ord_nonneg_of_mem hf
  have hlow : ∀ q, q < (v.ord f).toNat → taylorCoeff v t q f = 0 :=
    (forall_lt_taylorCoeff_eq_zero_iff_le_ord v hv ht hf hf0 _).mpr
      (by rw [Int.toNat_of_nonneg hford])
  intro hzero
  have hnext : ∀ q, q < (v.ord f).toNat + 1 → taylorCoeff v t q f = 0 := by
    intro q hq
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact hlow q hq
    · exact hzero
  have hnextOrd :=
    (forall_lt_taylorCoeff_eq_zero_iff_le_ord v hv ht hf hf0 ((v.ord f).toNat + 1)).mp hnext
  rw [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg hford] at hnextOrd
  omega

end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_ord_ne_zero
end ProofImplementation

end

section

/-!
# Place taylor Coeff smul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_smul

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorCoeff_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) (r : ℕ) :
    taylorCoeff v t r (c • f) = c * taylorCoeff v t r f := by
  rw [taylorCoeff_eq, taylorCoeff_eq, taylorRem_smul v hv ht hf c r]
  exact v.evalAt_smul_of_mem hv c (taylorRem_mem_toValuationSubring v hv ht hf r)
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_smul
end ProofImplementation

end

section

/-!
# Place taylor Coeff mul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_mul

open AlgebraicCurve AlgebraicCurve.Place

namespace ProofAuxJetT6
open AlgebraicCurve AlgebraicCurve.Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem taylorRem_one (v : Place K F) (t f : F) :
    taylorRem v t f 1 = (f - algebraMap K F (v.evalAt f)) * t⁻¹ := rfl

end ProofAuxJetT6

open ProofAuxJetT6 in
theorem _root_.AlgebraicCurve.Place.taylorCoeff_mul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorCoeff v t r (f * g)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, taylorCoeff v t x.1 f * taylorCoeff v t x.2 g
        := by
  induction r generalizing f g with
  | zero =>
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, taylorCoeff_zero, taylorCoeff_zero,
      taylorCoeff_zero]
    exact v.evalAt_mul hv hf hg
  | succ r ih =>
    have hf1 : taylorRem v t f 1 ∈ v.toValuationSubring := taylorRem_mem_toValuationSubring v hv ht
      hf 1
    have hg1 : taylorRem v t g 1 ∈ v.toValuationSubring := taylorRem_mem_toValuationSubring v hv ht
      hg 1
    have hrem : taylorRem v t (f * g) 1
        = f * taylorRem v t g 1 + (v.evalAt g) • taylorRem v t f 1 := by
      rw [taylorRem_one, taylorRem_one, taylorRem_one, v.evalAt_mul hv hf hg, map_mul,
        Algebra.smul_def]
      ring
    have hsm : (v.evalAt g) • taylorRem v t f 1 ∈ v.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) hf1
    rw [taylorCoeff_succ_eq_taylorCoeff_taylorRem_one, hrem,
      taylorCoeff_add v hv ht (mul_mem hf hg1) hsm r, taylorCoeff_smul v hv ht hf1 _ r,
      ih hf hg1, Finset.Nat.antidiagonal_succ', Finset.sum_cons, Finset.sum_map]
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst,
      Prod.map_snd,
      Function.Embedding.coe_refl, id_eq, Nat.succ_eq_add_one,
      taylorCoeff_succ_eq_taylorCoeff_taylorRem_one, taylorCoeff_zero]
    ring
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_mul
end ProofImplementation

end
