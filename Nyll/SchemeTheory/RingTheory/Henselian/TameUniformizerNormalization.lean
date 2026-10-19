/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalSimpleRoot
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Normalizing a tame power series by an actual change of parameter

A series of positive order prime to the characteristic becomes the pure
power of the parameter under a constructed algebra automorphism. Both the
coordinate change and its inverse preserve every series order.
-/

noncomputable section

namespace PowerSeries

variable {K : Type*} [Field K]

/-- The unit factor of a tame parameter has a unique root with any specified
nonzero residue root. -/
theorem existsUnique_tameUnitRoot (U : PowerSeries K) (e : ℕ)
    (he : (e : K) ≠ 0) (a : K) (ha : a ≠ 0)
    (hroot : a ^ e = constantCoeff U) :
    ∃! B : PowerSeries K, B ^ e = U ∧ constantCoeff B = a := by
  have he0 : e ≠ 0 := by
    intro h
    exact he (h ▸ Nat.cast_zero)
  let P : Polynomial (PowerSeries K) := Polynomial.X ^ e - Polynomial.C U
  have hP : P.Monic := Polynomial.monic_X_pow_sub_C _ he0
  have hmap : P.map constantCoeff =
      Polynomial.X ^ e - Polynomial.C (constantCoeff U) := by
    simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
  have hr : (P.map constantCoeff).eval a = 0 := by
    rw [hmap, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, hroot, sub_self]
  have hd : (P.map constantCoeff).derivative.eval a ≠ 0 := by
    rw [hmap, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_ne_zero he (pow_ne_zero _ ha)
  obtain ⟨B, hB, huniq⟩ := existsUnique_monic_root_of_constantCoeff P hP a hr hd
  have eval_iff (A : PowerSeries K) : P.eval A = 0 ↔ A ^ e = U := by
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero]
  refine ⟨B, ⟨(eval_iff B).mp hB.1, hB.2⟩, ?_⟩
  intro A hA
  exact huniq A ⟨(eval_iff A).mpr hA.1, hA.2⟩

/-- A nonzero tame series over an algebraically closed coefficient field has
an actual uniformizer root, whose linear coefficient is nonzero. -/
theorem exists_tameUniformizerRoot [IsAlgClosed K]
    (f : PowerSeries K) (e : ℕ) (he : (e : K) ≠ 0)
    (horder : f.order = (e : ℕ∞)) :
    ∃ P : PowerSeries K, constantCoeff P = 0 ∧
      IsUnit (coeff 1 P) ∧ P ^ e = f := by
  have he0 : e ≠ 0 := by
    intro h
    exact he (h ▸ Nat.cast_zero)
  have hf : f ≠ 0 := by
    intro h
    rw [h, order_zero] at horder
    exact ENat.top_ne_natCast e horder
  let U := divXPowOrder f
  have hU : constantCoeff U ≠ 0 :=
    fun h => hf (constantCoeff_divXPowOrder_eq_zero_iff.mp h)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (constantCoeff U) (Nat.pos_of_ne_zero he0)
  have ha0 : a ≠ 0 := by
    intro h
    exact hU (ha.symm.trans (by rw [h, zero_pow he0]))
  obtain ⟨B, hB, _⟩ := existsUnique_tameUnitRoot U e he a ha0 ha
  refine ⟨X * B, ?_, ?_, ?_⟩
  · rw [map_mul, constantCoeff_X, zero_mul]
  · have hc : coeff 1 (X * B) = a := by
      calc
        _ = coeff 0 B := by
          simpa only [pow_one, Nat.zero_add] using coeff_X_pow_mul B 1 0
        _ = a := by rw [coeff_zero_eq_constantCoeff, hB.2]
    rw [hc]
    exact isUnit_iff_ne_zero.mpr ha0
  · rw [mul_pow, hB.1]
    have hn : f.order.toNat = e := by rw [horder]; rfl
    exact hn ▸ X_pow_order_mul_divXPowOrder

/-- Substitution by a zero-constant series with invertible linear term is
an actual algebra automorphism, with the compositional inverse as inverse. -/
def parameterChange (P : PowerSeries K) (hP : constantCoeff P = 0)
    (hP' : IsUnit (coeff 1 P)) : PowerSeries K ≃ₐ[K] PowerSeries K where
  __ := substAlgHom (HasSubst.of_constantCoeff_zero' hP)
  invFun := subst (P.substInvOfIsUnit hP')
  left_inv f := by
    change PowerSeries.subst (P.substInvOfIsUnit hP')
      (substAlgHom (HasSubst.of_constantCoeff_zero' hP) f) = f
    rw [coe_substAlgHom]
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hP)
      (HasSubst.substInvOfIsUnit P hP'), subst_substInvOfIsUnit_right P hP hP', X_subst]
  right_inv f := by
    change substAlgHom (HasSubst.of_constantCoeff_zero' hP)
      (PowerSeries.subst (P.substInvOfIsUnit hP') f) = f
    rw [coe_substAlgHom]
    rw [subst_comp_subst_apply (HasSubst.substInvOfIsUnit P hP')
      (HasSubst.of_constantCoeff_zero' hP), subst_substInvOfIsUnit_left P hP hP', X_subst]

theorem parameterChange_apply (P : PowerSeries K) (hP : constantCoeff P = 0)
    (hP' : IsUnit (coeff 1 P)) (f : PowerSeries K) :
    parameterChange P hP hP' f = PowerSeries.subst P f :=
  congrFun (coe_substAlgHom (HasSubst.of_constantCoeff_zero' hP)) f

/-- Both parameter coordinates have the same order filtration. -/
theorem parameterChange_order (P : PowerSeries K) (hP : constantCoeff P = 0)
    (hP' : IsUnit (coeff 1 P)) (f : PowerSeries K) :
    (parameterChange P hP hP' f).order = f.order := by
  apply le_antisymm
  · have h := le_order_subst_left'
      (constantCoeff_substInvOfIsUnit P hP') (φ := parameterChange P hP hP' f)
    change (parameterChange P hP hP' f).order ≤
      ((parameterChange P hP hP').symm (parameterChange P hP hP' f)).order at h
    rw [AlgEquiv.symm_apply_apply] at h
    exact h
  · rw [parameterChange_apply]
    exact le_order_subst_left' hP

/-- The entire tame series, not just its leading term, becomes `X^e`. -/
theorem exists_tameNormalization [IsAlgClosed K]
    (f : PowerSeries K) (e : ℕ) (he : (e : K) ≠ 0)
    (horder : f.order = (e : ℕ∞)) :
    ∃ E : PowerSeries K ≃ₐ[K] PowerSeries K,
      E f = X ^ e ∧ ∀ A, (E A).order = A.order := by
  obtain ⟨P, hP, hP', hpow⟩ := exists_tameUniformizerRoot f e he horder
  let E := parameterChange P hP hP'
  refine ⟨E.symm, ?_, ?_⟩
  · apply E.injective
    rw [AlgEquiv.apply_symm_apply, map_pow]
    change f = (parameterChange P hP hP' X) ^ e
    rw [parameterChange_apply]
    rw [subst_X (HasSubst.of_constantCoeff_zero' hP)]
    exact hpow.symm
  · intro A
    exact (parameterChange_order P hP hP' (E.symm A)).symm.trans
      (congrArg PowerSeries.order (E.apply_symm_apply A))

end PowerSeries
