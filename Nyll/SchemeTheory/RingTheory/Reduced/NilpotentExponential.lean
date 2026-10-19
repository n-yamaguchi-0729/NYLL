/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Reduced.NilpotentPrincipalUnits
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.NormNum

/-!
# Exponential and logarithm for a nilpotent ideal in characteristic zero

The finite exponential identifies the additive group of a nilpotent ideal
with its actual principal units. Surjectivity and injectivity are proved by
induction on the nilpotence exponent, using the exact first-order term and
then the smaller ideal `I²`. The inverse therefore supplies a logarithm
without analytic convergence or a reducedness hypothesis.
-/

noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The finite exponential is exactly `1 + a` when the square vanishes. -/
theorem exp_eq_one_add_of_sq_zero {a : R} (ha : a ^ 2 = 0) :
    IsNilpotent.exp a = 1 + a := by
  rw [IsNilpotent.exp_eq_sum ha]
  norm_num [Finset.sum_range_succ]

/-- The higher exponential terms belong to the square of the original ideal. -/
theorem exp_sub_one_sub_mem_pow_two (I : Ideal R) {a : R}
    (ha : IsNilpotent a) (haI : a ∈ I) : IsNilpotent.exp a - 1 - a ∈ I ^ 2 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hsq : (Ideal.Quotient.mk (I ^ 2) a) ^ 2 = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow haI 2)
  rw [map_sub, map_sub, IsNilpotent.map_exp ha, map_one,
    exp_eq_one_add_of_sq_zero hsq]
  ring

private def nilpotentExpUnit (a : R) (ha : IsNilpotent a) : Rˣ where
  val := IsNilpotent.exp a
  inv := IsNilpotent.exp (-a)
  val_inv := IsNilpotent.exp_mul_exp_neg_self ha
  inv_val := IsNilpotent.exp_neg_mul_exp_self ha

/-- The finite exponential, as an actual homomorphism to principal units. -/
def principalUnitExp (I : Ideal R) (hI : IsNilpotent I) :
    Multiplicative I →* I.principalUnits where
  toFun a := ⟨nilpotentExpUnit (Multiplicative.toAdd a).1
    (isNilpotent_element_of_mem hI (Multiplicative.toAdd a).2), by
      apply (I.mem_principalUnits _).mpr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mk I (IsNilpotent.exp (Multiplicative.toAdd a).1 - 1) = 0
      rw [map_sub, map_one,
        IsNilpotent.map_exp (isNilpotent_element_of_mem hI (Multiplicative.toAdd a).2),
        Ideal.Quotient.eq_zero_iff_mem.mpr (Multiplicative.toAdd a).2,
        IsNilpotent.exp_zero, sub_self]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact IsNilpotent.exp_zero
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    exact IsNilpotent.exp_add_of_commute (Commute.all _ _)
      (isNilpotent_element_of_mem hI (Multiplicative.toAdd a).2)
      (isNilpotent_element_of_mem hI (Multiplicative.toAdd b).2)

private theorem exp_bijective_of_pow_eq_bot (N : ℕ) :
    ∀ (I : Ideal R), I ^ N = ⊥ →
      (∀ u : Rˣ, u ∈ I.principalUnits →
        ∃ a : R, a ∈ I ∧ IsNilpotent.exp a = (u : R)) ∧
      (∀ a : R, a ∈ I → IsNilpotent.exp a = 1 → a = 0) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro I hN
    by_cases hsmall : N ≤ 1
    · have hI : I = ⊥ := by
        apply le_bot_iff.mp
        calc
          I = I ^ 1 := (pow_one I).symm
          _ ≤ I ^ N := Ideal.pow_le_pow_right hsmall
          _ = ⊥ := hN
      constructor
      · intro u hu
        rw [hI, principalUnits_bot, Subgroup.mem_bot] at hu
        refine ⟨0, I.zero_mem, ?_⟩
        rw [IsNilpotent.exp_zero, hu, Units.val_one]
      · intro a ha _
        rw [hI, Ideal.mem_bot] at ha
        exact ha
    · have hsq : (I ^ 2) ^ (N - 1) = ⊥ := by
        apply le_bot_iff.mp
        rw [← pow_mul]
        calc
          I ^ (2 * (N - 1)) ≤ I ^ N := Ideal.pow_le_pow_right (by omega)
          _ = ⊥ := hN
      have hI : IsNilpotent I := ⟨N, hN⟩
      have hI₂ : IsNilpotent (I ^ 2) := ⟨N - 1, hsq⟩
      have hrec := ih (N - 1) (by omega) (I ^ 2) hsq
      constructor
      · intro u hu
        let a : R := (u : R) - 1
        have ha : a ∈ I := (I.mem_principalUnits u).mp hu
        have hnil : IsNilpotent a := isNilpotent_element_of_mem hI ha
        let E : Rˣ := nilpotentExpUnit a hnil
        let r : Rˣ := u / E
        have hr : r ∈ (I ^ 2).principalUnits := by
          have hdiff : (u : R) - IsNilpotent.exp a ∈ I ^ 2 := by
            have he : (u : R) - IsNilpotent.exp a =
                -(IsNilpotent.exp a - 1 - a) := by dsimp only [a]; ring
            rw [he]
            exact (I ^ 2).neg_mem (I.exp_sub_one_sub_mem_pow_two hnil ha)
          have he : Units.map (Ideal.Quotient.mk (I ^ 2)).toMonoidHom u =
              Units.map (Ideal.Quotient.mk (I ^ 2)).toMonoidHom E := by
            apply Units.ext
            exact Ideal.Quotient.eq.mpr hdiff
          change Units.map (Ideal.Quotient.mk (I ^ 2)).toMonoidHom (u / E) = 1
          rw [map_div, he, div_self']
        obtain ⟨b, hb, hexpb⟩ := hrec.1 r hr
        refine ⟨a + b, I.add_mem ha ((Ideal.pow_le_self two_ne_zero) hb), ?_⟩
        rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnil
          (isNilpotent_element_of_mem hI₂ hb), hexpb]
        change ((E * r : Rˣ) : R) = (u : R)
        apply congrArg Units.val
        dsimp only [r]
        rw [div_eq_mul_inv, mul_left_comm E u, mul_inv_cancel, mul_one]
      · intro a ha he
        have h₂ := I.exp_sub_one_sub_mem_pow_two (isNilpotent_element_of_mem hI ha) ha
        rw [he, sub_self, zero_sub] at h₂
        exact hrec.2 a ((I ^ 2).neg_mem_iff.mp h₂) he

/-- Exponential is bijective on the actual ideal and principal-unit group. -/
theorem principalUnitExp_bijective (I : Ideal R) (hI : IsNilpotent I) :
    Function.Bijective (I.principalUnitExp hI) := by
  obtain ⟨N, hN⟩ := hI
  have h := exp_bijective_of_pow_eq_bot (R := R) N I hN
  constructor
  · apply (I.principalUnitExp ⟨N, hN⟩).ker_eq_bot_iff.mp
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro ha
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      apply h.2 (Multiplicative.toAdd a).1 (Multiplicative.toAdd a).2
      exact congrArg (fun u : I.principalUnits => ((u.1 : Rˣ) : R)) ha
    · intro ha
      rw [ha, map_one]
  · intro u
    obtain ⟨a, ha, hea⟩ := h.1 u.1 u.2
    exact ⟨Multiplicative.ofAdd ⟨a, ha⟩, Subtype.ext (Units.ext hea)⟩

/-- The actual finite exponential is a group isomorphism; its inverse is
the nilpotent logarithm on the entire principal-unit group. -/
def principalUnitExpEquiv (I : Ideal R) (hI : IsNilpotent I) :
    Multiplicative I ≃* I.principalUnits :=
  MulEquiv.ofBijective (I.principalUnitExp hI) (I.principalUnitExp_bijective hI)

/-- Evaluation of the constructed isomorphism is the original finite exponential. -/
theorem principalUnitExpEquiv_val (I : Ideal R) (hI : IsNilpotent I) (a : I) :
    (((I.principalUnitExpEquiv hI (Multiplicative.ofAdd a)).1 : Rˣ) : R) =
      IsNilpotent.exp (a : R) := rfl

end Ideal
