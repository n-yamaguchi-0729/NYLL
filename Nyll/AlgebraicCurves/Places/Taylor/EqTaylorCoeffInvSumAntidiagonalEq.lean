/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Nyll.AlgebraicCurves.Places.Taylor.Taylor

/-!
# Place eq taylor Coeff inv of forall sum antidiagonal eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq

open AlgebraicCurve AlgebraicCurve.Place Polynomial

namespace JetBridge

theorem inv_mem_of_evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {s : F} (hs : s ∈ v.toValuationSubring)
    (hs0 : v.evalAt s ≠ 0) : s⁻¹ ∈ v.toValuationSubring := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨s, hs⟩ ≠ 0 := by
    rw [← v.algebraMap_evalAt hv hs]
    exact (_root_.map_ne_zero _).mpr hs0
  have hu : IsUnit (⟨s, hs⟩ : v.toValuationSubring) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : v.toValuationSubring) : F) = s := by rw [hu]
  have hinv : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = s⁻¹ := by
    have h1 : s * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [← hinv]
  exact ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).2

theorem eq_taylorCoeff_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {s : F} (hs : s ∈ v.toValuationSubring) (hs0 : v.evalAt s ≠ 0)
    (m : ℕ) (σ : ℕ → K)
    (hσ : ∀ r, r < m →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ x.1 * taylorCoeff v t x.2 s = if r = 0 then 1
        else 0) :
    ∀ r, r < m → σ r = taylorCoeff v t r s⁻¹ := by
  have hsinv : s⁻¹ ∈ v.toValuationSubring := inv_mem_of_evalAt_ne_zero v hv hs hs0
  have hs' : s ≠ 0 := by
    intro h0; apply hs0; rw [h0]
    have := taylorCoeff_algebraMap v t (0 : K) 0
    rw [map_zero] at this
    simpa using this
  have hτ : ∀ r, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, taylorCoeff v t x.1 s⁻¹ * taylorCoeff
    v t x.2 s
      = if r = 0 then 1 else 0 := by
    intro r
    rw [← taylorCoeff_mul v hv ht hsinv hs r, inv_mul_cancel₀ hs',
      show (1 : F) = algebraMap K F 1 from (map_one _).symm, taylorCoeff_algebraMap]
  have ha0 : taylorCoeff v t 0 s ≠ 0 := by rwa [taylorCoeff_zero]
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    have e1 := hσ r hr
    have e2 := hτ r
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Nat.sub_self]
      at e1 e2
    have hsum : ∑ k ∈ Finset.range r, σ k * taylorCoeff v t (r - k) s
        = ∑ k ∈ Finset.range r, taylorCoeff v t k s⁻¹ * taylorCoeff v t (r - k) s :=
      Finset.sum_congr rfl fun k hk =>
        by rw [ih k (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hk; omega)]
    rw [hsum] at e1
    have e3 : σ r * taylorCoeff v t 0 s = taylorCoeff v t r s⁻¹ * taylorCoeff v t 0 s := by
      have := e1.trans e2.symm
      exact add_left_cancel this
    exact mul_right_cancel₀ ha0 e3

end JetBridge

theorem _root_.AlgebraicCurve.Place.eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {s : F} (hs : s ∈ v.toValuationSubring) (hs0 : v.evalAt s ≠ 0)
    (m : ℕ) (σ : ℕ → K)
    (hσ : ∀ r, r < m →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ x.1 * taylorCoeff v t x.2 s = if r = 0 then 1
        else 0) :
    ∀ r, r < m → σ r = taylorCoeff v t r s⁻¹ :=
  JetBridge.eq_taylorCoeff_inv v hv ht hs hs0 m σ hσ
end AlgebraicCurves.Places.Proofs.Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
end ProofImplementation
