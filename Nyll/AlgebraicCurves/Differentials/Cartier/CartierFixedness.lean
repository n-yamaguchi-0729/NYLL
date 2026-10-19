/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_KwCartierDlogFixednessEngine.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Cartier.CartierCoordinates
import Nyll.AlgebraicCurves.Differentials.Logarithmic.Logarithmic

/-!
# Cartier Fixedness
-/

open Polynomial AlgebraicCurve.PthPower AlgebraicCurve.Cartier

noncomputable section

namespace AlgebraicCurve.CartierLogarithmic

section GenericModel

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- The universal polynomial with independently varying coefficients and degrees below the
characteristic. -/
def genericPolynomial : Polynomial (MvPolynomial (Fin ℓ) ℤ) :=
  ∑ i : Fin ℓ, C (MvPolynomial.X i) * X ^ (i : ℕ)

/-- The universal polynomial with coefficient and variable exponents multiplied by the
characteristic. -/
def frobeniusPolynomial : Polynomial (MvPolynomial (Fin ℓ) ℤ) :=
  ∑ i : Fin ℓ, C (MvPolynomial.X i ^ ℓ) * X ^ (ℓ * (i : ℕ))

theorem map_pow_sub_frobeniusPolynomial_eq_zero :
    (genericPolynomial ℓ ^ ℓ - frobeniusPolynomial ℓ).map
      (MvPolynomial.map (Int.castRingHom (ZMod ℓ))) = 0 := by
  have : CharP (MvPolynomial (Fin ℓ) (ZMod ℓ)) ℓ :=
    charP_of_injective_ringHom (MvPolynomial.C_injective (Fin ℓ) (ZMod ℓ)) ℓ
  have : CharP (Polynomial (MvPolynomial (Fin ℓ) (ZMod ℓ))) ℓ :=
    charP_of_injective_ringHom (Polynomial.C_injective
      (R := MvPolynomial (Fin ℓ) (ZMod ℓ))) ℓ
  rw [Polynomial.map_sub, Polynomial.map_pow, sub_eq_zero]
  have hG : (genericPolynomial ℓ).map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))
      = ∑ i : Fin ℓ, C (MvPolynomial.X i) * X ^ (i : ℕ) := by
    rw [genericPolynomial, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      MvPolynomial.map_X]
  have hGpow : (frobeniusPolynomial ℓ).map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))
      = ∑ i : Fin ℓ, C (MvPolynomial.X i ^ ℓ) * X ^ (ℓ * (i : ℕ)) := by
    rw [frobeniusPolynomial, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      map_pow, MvPolynomial.map_X]
  rw [hG, hGpow, sum_pow_char]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, Nat.mul_comm (i : ℕ) ℓ]

theorem char_dvd_coeff_pow_sub_frobeniusPolynomial (k : ℕ) :
    MvPolynomial.C ((ℓ : ℕ) : ℤ) ∣ (genericPolynomial ℓ ^ ℓ - frobeniusPolynomial ℓ).coeff k := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have h1 : MvPolynomial.map (Int.castRingHom (ZMod ℓ))
      ((genericPolynomial ℓ ^ ℓ - frobeniusPolynomial ℓ).coeff k) = 0 := by
    have h := congrArg (fun p => p.coeff k) (map_pow_sub_frobeniusPolynomial_eq_zero ℓ)
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using h
  rw [MvPolynomial.C_dvd_iff_dvd_coeff]
  intro mono
  have h2 : ((((genericPolynomial ℓ ^ ℓ - frobeniusPolynomial ℓ).coeff k).coeff mono : ℤ)
      : ZMod ℓ) = 0 := by
    have h := congrArg (fun p => p.coeff mono) h1
    have hzero : (0 : MvPolynomial (Fin ℓ) (ZMod ℓ)).coeff mono = 0 := rfl
    simpa only [MvPolynomial.coeff_map, Int.coe_castRingHom, hzero] using h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h2
omit hℓ in
theorem derivative_genericPolynomial :
    derivative (genericPolynomial ℓ)
      = ∑ i : Fin ℓ, C (MvPolynomial.X i * ((i : ℕ) : MvPolynomial (Fin ℓ) ℤ))
          * X ^ ((i : ℕ) - 1) := by
  rw [genericPolynomial, derivative_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul_X_pow]

theorem coeff_pow_mul_derivative_eq_add_char_mul (m : ℕ) (hm : m + 1 < ℓ) :
    ∃ e : MvPolynomial (Fin ℓ) ℤ,
      (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).coeff (ℓ * m + (ℓ - 1))
        = ((m + 1 : ℕ) : MvPolynomial (Fin ℓ) ℤ)
            * MvPolynomial.X (⟨m + 1, hm⟩ : Fin ℓ) ^ ℓ
          + ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ) * e := by
  have hpos := hℓ.out.pos
  have h2 := hℓ.out.two_le
  have hsucc : ℓ - 1 + 1 = ℓ := by omega
  have hpow : genericPolynomial ℓ ^ ℓ = genericPolynomial ℓ ^ ((ℓ - 1) + 1) := by
    rw [hsucc]
  have ha : derivative (genericPolynomial ℓ ^ ℓ)
      = C ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
          * (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)) := by
    rw [hpow, derivative_pow_succ, mul_assoc, ← Nat.cast_add_one, hsucc]
  have hb : derivative (genericPolynomial ℓ ^ ℓ)
      = derivative (frobeniusPolynomial ℓ)
        + derivative (genericPolynomial ℓ ^ ℓ - frobeniusPolynomial ℓ) := by
    rw [derivative_sub]
    ring
  have hc2 : (derivative (frobeniusPolynomial ℓ)).coeff (ℓ * m + (ℓ - 1))
      = MvPolynomial.X (⟨m + 1, hm⟩ : Fin ℓ) ^ ℓ
          * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
    rw [frobeniusPolynomial, derivative_sum]
    have hterm : ∀ i : Fin ℓ,
        derivative (C (MvPolynomial.X i ^ ℓ) * X ^ (ℓ * (i : ℕ))
          : Polynomial (MvPolynomial (Fin ℓ) ℤ))
        = C (MvPolynomial.X i ^ ℓ * ((ℓ * (i : ℕ) : ℕ) : MvPolynomial (Fin ℓ) ℤ))
            * X ^ (ℓ * (i : ℕ) - 1) := fun i => derivative_C_mul_X_pow _ _
    rw [Finset.sum_congr rfl fun i _ => hterm i, finsetSum_coeff]
    rw [Finset.sum_eq_single (⟨m + 1, hm⟩ : Fin ℓ)]
    · have hval : (((⟨m + 1, hm⟩ : Fin ℓ) : ℕ)) = m + 1 := rfl
      have hidx : ℓ * m + (ℓ - 1) = ℓ * (((⟨m + 1, hm⟩ : Fin ℓ) : ℕ)) - 1 := by
        rw [hval, Nat.mul_succ]
        omega
      rw [coeff_C_mul, coeff_X_pow, ite_eq_left hidx, mul_one, hval]
    · intro j _ hji
      have hne : ℓ * m + (ℓ - 1) ≠ ℓ * (j : ℕ) - 1 := by
        intro heq
        rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
        · rw [hj0, Nat.mul_zero, Nat.zero_sub] at heq
          omega
        · have hj1 : ℓ * (j : ℕ) - 1 + 1 = ℓ * (j : ℕ) :=
            Nat.succ_pred_eq_of_pos (Nat.mul_pos hpos hjpos)
          have hlm : ℓ * m + (ℓ - 1) + 1 = ℓ * (m + 1) := by
            rw [Nat.mul_succ]
            omega
          have hmul : ℓ * (m + 1) = ℓ * (j : ℕ) := by omega
          have hjm : m + 1 = (j : ℕ) := Nat.eq_of_mul_eq_mul_left hpos hmul
          exact hji (Fin.ext hjm.symm)
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right hne, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hn1 : ℓ * m + (ℓ - 1) + 1 = ℓ * (m + 1) := by
    rw [Nat.mul_succ]
    omega
  obtain ⟨e₀, he₀⟩ := char_dvd_coeff_pow_sub_frobeniusPolynomial ℓ (ℓ * (m + 1))
  have hc3 : (derivative (genericPolynomial ℓ ^ ℓ - frobeniusPolynomial ℓ)).coeff (ℓ * m + (ℓ - 1))
      = MvPolynomial.C ((ℓ : ℕ) : ℤ) * e₀
          * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
    have hcast : ((ℓ * m + (ℓ - 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) + 1
        = ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
      exact_mod_cast congrArg (Nat.cast (R := MvPolynomial (Fin ℓ) ℤ)) hn1
    rw [coeff_derivative, show ℓ * m + (ℓ - 1) + 1 = ℓ * (m + 1) from hn1, he₀, hcast]
  have hCl : (MvPolynomial.C ((ℓ : ℕ) : ℤ) : MvPolynomial (Fin ℓ) ℤ)
      = ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ) := map_natCast MvPolynomial.C ℓ
  have hkey : ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
        * (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).coeff (ℓ * m + (ℓ - 1))
      = MvPolynomial.X (⟨m + 1, hm⟩ : Fin ℓ) ^ ℓ
          * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ)
        + MvPolynomial.C ((ℓ : ℕ) : ℤ) * e₀
            * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
    calc ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
          * (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).coeff
              (ℓ * m + (ℓ - 1))
        = (C ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
            * (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ))).coeff
              (ℓ * m + (ℓ - 1)) := by
          rw [coeff_C_mul]
      _ = (derivative (genericPolynomial ℓ ^ ℓ)).coeff (ℓ * m + (ℓ - 1)) := by rw [← ha]
      _ = (derivative (frobeniusPolynomial ℓ)).coeff (ℓ * m + (ℓ - 1))
            + (derivative (genericPolynomial ℓ ^ ℓ - frobeniusPolynomial ℓ)).coeff
                (ℓ * m + (ℓ - 1)) := by
          rw [hb, coeff_add]
      _ = _ := by rw [hc2, hc3]
  have hne : ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ) ≠ 0 := by
    rw [← hCl]
    exact MvPolynomial.C_ne_zero.mpr
      (Int.natCast_ne_zero.mpr hℓ.out.ne_zero)
  refine ⟨e₀ * ((m + 1 : ℕ) : MvPolynomial (Fin ℓ) ℤ), mul_left_cancel₀ hne ?_⟩
  rw [hkey, hCl]
  push_cast
  ring

theorem natDegree_pow_mul_derivative_le :
    (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).natDegree ≤ ℓ * (ℓ - 1) := by
  have hG : (genericPolynomial ℓ).natDegree ≤ ℓ - 1 := by
    rw [genericPolynomial]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    have := i.isLt
    omega
  have hG' : (derivative (genericPolynomial ℓ)).natDegree ≤ ℓ - 1 := by
    rw [derivative_genericPolynomial]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    have := i.isLt
    omega
  have hpow : (genericPolynomial ℓ ^ (ℓ - 1)).natDegree ≤ (ℓ - 1) * (ℓ - 1) :=
    le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left _ hG)
  have hmul := Polynomial.natDegree_mul_le
    (p := genericPolynomial ℓ ^ (ℓ - 1)) (q := derivative (genericPolynomial ℓ))
  have hsucc : ℓ - 1 + 1 = ℓ := by have := hℓ.out.pos; omega
  have harith : (ℓ - 1) * (ℓ - 1) + (ℓ - 1) = ℓ * (ℓ - 1) := by
    calc (ℓ - 1) * (ℓ - 1) + (ℓ - 1) = ((ℓ - 1) + 1) * (ℓ - 1) := by ring
      _ = ℓ * (ℓ - 1) := by rw [hsucc]
  omega

theorem coeff_pow_mul_derivative_eq_zero (m : ℕ) (hm : ℓ ≤ m + 1) :
    (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).coeff
      (ℓ * m + (ℓ - 1)) = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_pow_mul_derivative_le ℓ) ?_)
  have h2 := hℓ.out.two_le
  have hmm : ℓ - 1 ≤ m := by omega
  have h3 : ℓ * (ℓ - 1) ≤ ℓ * m := Nat.mul_le_mul_left ℓ hmm
  omega

end GenericModel

section Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

/-- The characteristic power regarded as an element of the subfield of characteristic powers. -/
def pthPower (t : F) : pthPowers F ℓ :=
  ⟨t ^ ℓ, (mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩
@[simp]
theorem coe_pthPower (t : F) : ((pthPower (ℓ := ℓ) t : pthPowers F ℓ)
    : F) = t ^ ℓ := rfl

/-- Extend the finite coefficient vector by zero outside its index range. -/
def extendCoefficients (v : Fin ℓ → pthPowers F ℓ) (n : ℕ) :
    pthPowers F ℓ :=
  if h : n < ℓ then v ⟨n, h⟩ else 0

theorem extendCoefficients_of_lt (v : Fin ℓ → pthPowers F ℓ) {n : ℕ} (h : n < ℓ) :
    extendCoefficients v n = v ⟨n, h⟩ := by
  rw [extendCoefficients, dite_eq_left h]

/-- Evaluation of the universal coefficient variables at the given characteristic-power
coefficients. -/
def coefficientEval (v : Fin ℓ → pthPowers F ℓ) :
    MvPolynomial (Fin ℓ) ℤ →+* pthPowers F ℓ :=
  (MvPolynomial.aeval v).toRingHom

theorem coefficientEval_X (v : Fin ℓ → pthPowers F ℓ) (j : Fin ℓ) :
    coefficientEval v (MvPolynomial.X j) = v j := by
  exact MvPolynomial.aeval_X v j

/-- The coefficient evaluation followed by the inclusion into the ambient field. -/
def coefficientEvalToField (v : Fin ℓ → pthPowers F ℓ) :
    MvPolynomial (Fin ℓ) ℤ →+* F :=
  ((pthPowers F ℓ).subtype).comp (coefficientEval v)

theorem coefficientEvalToField_apply (v : Fin ℓ → pthPowers F ℓ)
    (x : MvPolynomial (Fin ℓ) ℤ) :
    coefficientEvalToField v x = ((coefficientEval v x : pthPowers F ℓ) : F) := by
  rfl

/-- Evaluation of the universal polynomial at the chosen coordinate and coefficient vector. -/
def polynomialEval (t : F) (v : Fin ℓ → pthPowers F ℓ) :
    Polynomial (MvPolynomial (Fin ℓ) ℤ) →+* F :=
  Polynomial.eval₂RingHom (coefficientEvalToField v) t

theorem polynomialEval_apply (t : F) (v : Fin ℓ → pthPowers F ℓ)
    (q : Polynomial (MvPolynomial (Fin ℓ) ℤ)) :
    polynomialEval t v q = Polynomial.eval₂ (coefficientEvalToField v) t q := by
  rfl

theorem natCast_pow_char (n : ℕ) : ((n : F)) ^ ℓ = (n : F) := by
  have h := map_natCast (frobenius F ℓ) n
  rwa [frobenius_def] at h

theorem polynomialEval_genericPolynomial (t : F)
    (hsep : ∀ x : F, IsSeparable (adjoinPthPowers (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (pthPowers F ℓ) t).natDegree = ℓ)
    (f : F) :
    polynomialEval t (powerCoefficients t hsep hdeg f) (genericPolynomial ℓ) = f := by
  rw [genericPolynomial, map_sum]
  have hterm : ∀ i : Fin ℓ,
      polynomialEval t (powerCoefficients t hsep hdeg f) (C (MvPolynomial.X i) * X ^ (i : ℕ))
        = ((powerCoefficients t hsep hdeg f i : F)) * t ^ (i : ℕ) := by
    intro i
    rw [map_mul, map_pow, polynomialEval_apply, polynomialEval_apply, eval₂_C, eval₂_X,
      coefficientEvalToField_apply, coefficientEval_X]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact (powerCoefficients_spec t hsep hdeg f).symm

/-- The formal derivative evaluated at the chosen coordinate for the polynomial with the given
coefficients. -/
def derivativeEval (t : F) (v : Fin ℓ → pthPowers F ℓ) : F :=
  ∑ i : Fin ℓ, ((i : ℕ) : F) * ((v i : F)) * t ^ ((i : ℕ) - 1)

theorem polynomialEval_derivative (t : F) (v : Fin ℓ → pthPowers F ℓ) :
    polynomialEval t v (derivative (genericPolynomial ℓ)) = derivativeEval t v := by
  rw [derivative_genericPolynomial, map_sum, derivativeEval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, polynomialEval_apply, polynomialEval_apply, eval₂_C, eval₂_X,
    map_mul, map_natCast, coefficientEvalToField_apply, coefficientEval_X]
  ring

theorem powerCoefficients_polynomialEval (t : F)
    (hsep : ∀ x : F, IsSeparable (adjoinPthPowers (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (pthPowers F ℓ) t).natDegree = ℓ)
    (v : Fin ℓ → pthPowers F ℓ)
    (q : Polynomial (MvPolynomial (Fin ℓ) ℤ)) (N : ℕ) (hN : q.natDegree < ℓ * N) :
    powerCoefficients t hsep hdeg (polynomialEval t v q)
      = fun r : Fin ℓ => ∑ m ∈ Finset.range N,
          coefficientEval v (q.coeff (ℓ * m + (r : ℕ))) * pthPower (ℓ := ℓ) t ^ m := by
  have hpos := hℓ.out.pos
  refine powerCoefficients_unique t hsep hdeg ?_
  have h0 : polynomialEval t v q
      = ∑ k ∈ Finset.range (ℓ * N), coefficientEvalToField v (q.coeff k) * t ^ k := by
    rw [polynomialEval_apply]
    exact eval₂_eq_sum_range' (coefficientEvalToField v) hN t
  calc polynomialEval t v q
      = ∑ k ∈ Finset.range (ℓ * N), coefficientEvalToField v (q.coeff k) * t ^ k := h0
    _ = ∑ p ∈ Finset.range N ×ˢ Finset.range ℓ,
          coefficientEvalToField v (q.coeff (ℓ * p.1 + p.2)) * t ^ (ℓ * p.1 + p.2) := by
        refine Finset.sum_nbij' (fun k => (k / ℓ, k % ℓ)) (fun p => ℓ * p.1 + p.2)
          ?_ ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_range] at hk
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
          refine ⟨?_, Nat.mod_lt _ hpos⟩
          rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm N ℓ]
          exact hk
        · intro p hp
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
          rw [Finset.mem_range]
          show ℓ * p.1 + p.2 < ℓ * N
          have h1 : p.1 + 1 ≤ N := hp.1
          have h2 : ℓ * (p.1 + 1) ≤ ℓ * N := Nat.mul_le_mul_left ℓ h1
          rw [Nat.mul_succ] at h2
          omega
        · intro k _
          exact Nat.div_add_mod k ℓ
        · intro p hp
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
          have hd : (ℓ * p.1 + p.2) / ℓ = p.1 := by
            rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hp.2, Nat.add_zero]
          have hm : (ℓ * p.1 + p.2) % ℓ = p.2 := by
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp.2]
          exact Prod.ext hd hm
        · intro k _
          change coefficientEvalToField v (q.coeff k) * t ^ k
              = coefficientEvalToField v (q.coeff (ℓ * (k / ℓ) + k % ℓ))
                  * t ^ (ℓ * (k / ℓ) + k % ℓ)
          rw [Nat.div_add_mod k ℓ]
    _ = ∑ m ∈ Finset.range N, ∑ r ∈ Finset.range ℓ,
          coefficientEvalToField v (q.coeff (ℓ * m + r)) * t ^ (ℓ * m + r) :=
        Finset.sum_product _ _ _
    _ = ∑ r ∈ Finset.range ℓ, ∑ m ∈ Finset.range N,
          coefficientEvalToField v (q.coeff (ℓ * m + r)) * t ^ (ℓ * m + r) :=
        Finset.sum_comm
    _ = ∑ r ∈ Finset.range ℓ,
          (∑ m ∈ Finset.range N, coefficientEvalToField v (q.coeff (ℓ * m + r)) * (t ^ ℓ) ^ m)
            * t ^ r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [pow_add, pow_mul, mul_assoc]
    _ = ∑ i : Fin ℓ,
          (((fun r : Fin ℓ => ∑ m ∈ Finset.range N,
              coefficientEval v (q.coeff (ℓ * m + (r : ℕ)))
                * pthPower (ℓ := ℓ) t ^ m) i : pthPowers F ℓ) : F)
            * t ^ (i : ℕ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun r =>
          (∑ m ∈ Finset.range N, coefficientEvalToField v (q.coeff (ℓ * m + r)) * (t ^ ℓ) ^ m)
            * t ^ r) ℓ]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [coefficientEvalToField_apply, coe_pthPower]

end Transport

section Assembly

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

theorem D_eq_derivativeEval_smul (t : F)
    (hsep : ∀ x : F, IsSeparable (adjoinPthPowers (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (pthPowers F ℓ) t).natDegree = ℓ)
    (f : F) :
    KaehlerDifferential.D K F f
      = derivativeEval t (powerCoefficients t hsep hdeg f)
          • KaehlerDifferential.D K F t := by
  conv_lhs => rw [powerCoefficients_spec t hsep hdeg f]
  rw [map_sum, derivativeEval, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Derivation.leibniz]
  have hDv : KaehlerDifferential.D K F ((powerCoefficients t hsep hdeg f i : F)) = 0 := by
    rw [← pthRoot_pow (powerCoefficients t hsep hdeg f i)]
    exact D_pow_char _
  rw [hDv, smul_zero, add_zero, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F,
    smul_smul, smul_smul]
  congr 1
  ring

theorem derivativeEval_pow_char (t : F) (v : Fin ℓ → pthPowers F ℓ) :
    derivativeEval t v ^ ℓ
      = ((∑ m ∈ Finset.range (ℓ - 1),
            ((m + 1 : ℕ) : pthPowers F ℓ) * extendCoefficients v (m + 1) ^ ℓ
              * pthPower (ℓ := ℓ) t ^ m : pthPowers F ℓ) : F) := by
  have h2 := hℓ.out.two_le
  have hℓ1 : ℓ - 1 + 1 = ℓ := by omega
  have hR : ((∑ m ∈ Finset.range (ℓ - 1),
        ((m + 1 : ℕ) : pthPowers F ℓ) * extendCoefficients v (m + 1) ^ ℓ
          * pthPower (ℓ := ℓ) t ^ m : pthPowers F ℓ) : F)
      = ∑ m ∈ Finset.range (ℓ - 1),
          ((m + 1 : ℕ) : F) * ((extendCoefficients v (m + 1) : F)) ^ ℓ * (t ^ ℓ) ^ m := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coe_pthPower]
  rw [hR, derivativeEval, sum_pow_char]
  have hterm : ∀ i : Fin ℓ,
      (((i : ℕ) : F) * ((v i : F)) * t ^ ((i : ℕ) - 1)) ^ ℓ
        = ((i : ℕ) : F) * ((extendCoefficients v (i : ℕ) : F)) ^ ℓ * (t ^ ℓ) ^ ((i : ℕ) - 1) := by
    intro i
    rw [mul_pow, mul_pow, natCast_pow_char, ← pow_mul,
      Nat.mul_comm ((i : ℕ) - 1) ℓ, pow_mul, extendCoefficients_of_lt v i.isLt, Fin.eta]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    ((k : ℕ) : F) * ((extendCoefficients v k : F)) ^ ℓ * (t ^ ℓ) ^ (k - 1)) ℓ]
  have hrange : Finset.range ℓ = Finset.range ((ℓ - 1) + 1) := by rw [hℓ1]
  rw [hrange, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel]

theorem powerCoefficients_pow_mul_derivative_last (t : F)
    (hsep : ∀ x : F, IsSeparable (adjoinPthPowers (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (pthPowers F ℓ) t).natDegree = ℓ)
    (v : Fin ℓ → pthPowers F ℓ) :
    powerCoefficients t hsep hdeg
        (polynomialEval t v (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)))
        ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩
      = ∑ m ∈ Finset.range (ℓ - 1),
          ((m + 1 : ℕ) : pthPowers F ℓ) * extendCoefficients v (m + 1) ^ ℓ
            * pthPower (ℓ := ℓ) t ^ m := by
  have hpos := hℓ.out.pos
  have h2 := hℓ.out.two_le
  have hℓ1 : ℓ - 1 + 1 = ℓ := by omega
  have hmulsq : ℓ * ℓ = ℓ * (ℓ - 1) + ℓ := by
    calc ℓ * ℓ = ℓ * ((ℓ - 1) + 1) := by rw [hℓ1]
      _ = ℓ * (ℓ - 1) + ℓ := by rw [Nat.mul_succ]
  have hdeg' : (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).natDegree
      < ℓ * ℓ := by
    have h := natDegree_pow_mul_derivative_le ℓ
    omega
  have ht3 := powerCoefficients_polynomialEval t hsep hdeg v
    (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)) ℓ hdeg'
  rw [ht3]
  change ∑ m ∈ Finset.range ℓ,
      coefficientEval v ((genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).coeff
        (ℓ * m + (ℓ - 1))) * pthPower (ℓ := ℓ) t ^ m = _
  have hrange : Finset.range ℓ = Finset.range ((ℓ - 1) + 1) := by rw [hℓ1]
  rw [hrange, Finset.sum_range_succ]
  have htop : (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)).coeff
      (ℓ * (ℓ - 1) + (ℓ - 1)) = 0 :=
    coeff_pow_mul_derivative_eq_zero ℓ (ℓ - 1) (by omega)
  rw [htop, map_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmlt : m + 1 < ℓ := by
    rw [Finset.mem_range] at hm
    omega
  obtain ⟨e, he⟩ := coeff_pow_mul_derivative_eq_add_char_mul ℓ m hmlt
  rw [he, map_add, map_mul, map_mul, map_natCast, map_natCast, map_pow, coefficientEval_X]
  have hl0 : ((ℓ : ℕ) : pthPowers F ℓ) = 0 := by
    have h1 : (((ℓ : ℕ) : pthPowers F ℓ) : F) = ((ℓ : ℕ) : F) := by
      norm_cast
    have hF : ((ℓ : ℕ) : F) = 0 := CharP.cast_eq_zero F ℓ
    exact ZeroMemClass.coe_eq_zero.mp (h1.trans hF)
  rw [hl0, zero_mul, add_zero, extendCoefficients_of_lt v hmlt]

theorem cartier_dlog (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (adjoinPthPowers (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (pthPowers F ℓ) t).natDegree = ℓ)
    {f : F} (hf : f ≠ 0) :
    cartier (K := K) t hdt hspan hsep hdeg (dlog K f)
      = dlog K f := by
  have hpos := hℓ.out.pos
  have hℓ1 : ℓ - 1 + 1 = ℓ := by omega
  set v : Fin ℓ → pthPowers F ℓ := powerCoefficients t hsep hdeg f with hv
  have hdlog : dlog K f
      = (f⁻¹ * derivativeEval t v) • KaehlerDifferential.D K F t := by
    rw [dlog, D_eq_derivativeEval_smul t hsep hdeg f, smul_smul]
  have hsplit : f⁻¹ * derivativeEval t v
      = (f⁻¹) ^ ℓ * (f ^ (ℓ - 1) * derivativeEval t v) := by
    have h1 : (f⁻¹) ^ ℓ * f ^ (ℓ - 1) = f⁻¹ := by
      have hfpow : (f⁻¹) ^ ℓ = (f⁻¹) ^ ((ℓ - 1) + 1) := by rw [hℓ1]
      calc (f⁻¹) ^ ℓ * f ^ (ℓ - 1)
          = f⁻¹ * ((f⁻¹) ^ (ℓ - 1) * f ^ (ℓ - 1)) := by
            rw [hfpow, pow_succ]
            ring
        _ = f⁻¹ * ((f⁻¹ * f) ^ (ℓ - 1)) := by rw [mul_pow]
        _ = f⁻¹ := by rw [inv_mul_cancel₀ hf, one_pow, mul_one]
    calc f⁻¹ * derivativeEval t v
        = ((f⁻¹) ^ ℓ * f ^ (ℓ - 1)) * derivativeEval t v := by rw [h1]
      _ = (f⁻¹) ^ ℓ * (f ^ (ℓ - 1) * derivativeEval t v) := by ring
  have hω : dlog K f
      = (f⁻¹) ^ ℓ • ((f ^ (ℓ - 1) * derivativeEval t v)
          • KaehlerDifferential.D K F t) := by
    rw [hdlog, hsplit, mul_smul]
  conv_lhs => rw [hω]
  rw [cartier_pow_smul]
  have hcoord : differentialCoordinate t hdt hspan
      ((f ^ (ℓ - 1) * derivativeEval t v) • KaehlerDifferential.D K F t)
      = f ^ (ℓ - 1) * derivativeEval t v :=
    differentialCoordinate_unique t hdt hspan rfl
  have hPhi : f ^ (ℓ - 1) * derivativeEval t v
      = polynomialEval t v (genericPolynomial ℓ ^ (ℓ - 1) * derivative (genericPolynomial ℓ)) := by
    rw [map_mul, map_pow, polynomialEval_genericPolynomial t hsep hdeg f, polynomialEval_derivative]
  have hroot : pthRoot (powerCoefficients t hsep hdeg
        (f ^ (ℓ - 1) * derivativeEval t v)
        ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩)
      = derivativeEval t v := by
    refine pthRoot_unique ?_
    rw [hPhi, powerCoefficients_pow_mul_derivative_last t hsep hdeg v]
    exact derivativeEval_pow_char t v
  rw [cartier, hcoord, hroot, smul_smul]
  exact hdlog.symm

end Assembly

end AlgebraicCurve.CartierLogarithmic

end
