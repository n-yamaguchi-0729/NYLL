/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.ValuedFieldTheory.Valuation.Subring.Integral.NormalizedPolynomial
public import Nyll.ValuedFieldTheory.Valuation.Subring.Integral.AevalDivEqAevalDivAddAevalInvDiv

/-!
# Valuation Subring exists aeval div eq aeval div add inv pow mul add aeval inv
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv

open Polynomial

namespace E4Sol

open ValuationSubring.NormalizedPolynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

variable {F : Type*} [Field F] [Algebra L F]

theorem IsLam.exists_eq_aeval_add_pow_mul {g x : F} (hg : Transcendental L g)
    (hx : IsLam A g x) (m : ℕ) :
    ∃ r : L[X], ACoeff A r ∧ r.degree < m ∧ ∃ x', IsLam A g x' ∧ x = aeval g r + g ^ m * x' := by
  induction m with
  | zero =>
    refine ⟨0, ACoeff.zero A, ?_, x, hx, ?_⟩
    · rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe 0
    · rw [map_zero, pow_zero, one_mul, zero_add]
  | succ m ih =>
    obtain ⟨r, hr, hrdeg, x', hx', hxe⟩ := ih
    obtain ⟨a, haA, x'', hx'', hx'e⟩ := hx'.exists_eq_add_mul A hg
    refine ⟨r + Polynomial.C a * X ^ m, ACoeff.add A hr (ACoeff.mul A (ACoeff.C A haA)
      (ACoeff.X_pow A m)), ?_, x'', hx'', ?_⟩
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le hrdeg (by exact_mod_cast Nat.le_succ m)
      · calc (Polynomial.C a * X ^ m).degree ≤ (m : WithBot ℕ) := degree_C_mul_X_pow_le m a
          _ < ((m + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
    · rw [hxe, hx'e]
      simp only [map_add, map_mul, aeval_C, aeval_X_pow]
      ring

end E4Sol

open E4Sol ValuationSubring.NormalizedPolynomial in
theorem _root_.ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ j, p.coeff j ∈ A)
    (ht : ∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1)
    (m : ℕ) :
    ∃ p₁ t₁ q s r : L[X],
      (∀ j, p₁.coeff j ∈ A) ∧ (∀ j, q.coeff j ∈ A) ∧ (∀ j, r.coeff j ∈ A) ∧ r.degree < m ∧
      (A.valuation (t₁.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t₁.coeff j) < 1) ∧
      (A.valuation (s.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (s.coeff j) < 1) ∧
      aeval f p / aeval f t =
        aeval f p₁ / aeval f t₁ + (f⁻¹) ^ m * (aeval f⁻¹ q / aeval f⁻¹ s) + aeval f⁻¹ r := by
  have hfi : Transcendental L f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  obtain ⟨p₁, t₁, q₀, s₀, hp₁, hq₀, ht₁, hs₀, hdec⟩ :=
    ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div A hf p t hp ht
  have hlam : IsLam A f⁻¹ (aeval f⁻¹ q₀ / aeval f⁻¹ s₀) :=
    ⟨q₀, s₀, hq₀, hs₀, div_mul_cancel₀ _ (aeval_ne_zero_of_isGood A hfi hs₀)⟩
  obtain ⟨r, hr, hrdeg, x', ⟨q, s, hq, hs, hx'e⟩, hxe⟩ :=
    IsLam.exists_eq_aeval_add_pow_mul A hfi hlam m
  refine ⟨p₁, t₁, q, s, r, hp₁, hq, hr, hrdeg, ht₁, hs, ?_⟩
  rw [hdec, hxe, eq_div_iff (aeval_ne_zero_of_isGood A hfi hs) |>.mpr hx'e]
  ring
end ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
