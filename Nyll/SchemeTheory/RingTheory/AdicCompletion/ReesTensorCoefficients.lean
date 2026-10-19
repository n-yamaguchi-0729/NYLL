/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AssociatedGradedModule
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.ReesAlgebra

/-!
# Actual coefficients after tensoring the Rees algebra

The coefficient map identifies the original Rees algebra with the direct
sum of its ideal powers. Tensoring this constructed equivalence and using
the native tensor/direct-sum equivalence gives the original tensor product
as the direct sum of the tensor products with those ideal powers.

No flatness is required. In particular, one forms the original Rees image
before tensoring with a module annihilated by the original ideal. The
positive-degree coefficient modules are retained in this order.
-/

noncomputable section

open scoped DirectSum TensorProduct

namespace ReesTensorCoefficients

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)

private def powerFiltration : I.Filtration R where
  N n := I ^ n
  mono n := Ideal.pow_le_pow_right (Nat.le_succ n)
  smul_le n := by
    rw [Ideal.smul_eq_mul, pow_succ']

private def polynomialModuleEquiv :
    ↥(reesAlgebra I) ≃ₗ[R] (powerFiltration I).submodule where
  toFun p := ⟨(PolynomialModule.equivPolynomial (R := R) (S := R)).symm p.val,
    fun n => p.property n⟩
  invFun p := ⟨PolynomialModule.equivPolynomial p.val, fun n => p.property n⟩
  left_inv p := Subtype.ext
    ((PolynomialModule.equivPolynomial (R := R) (S := R)).apply_symm_apply p.val)
  right_inv p := Subtype.ext
    ((PolynomialModule.equivPolynomial (R := R) (S := R)).symm_apply_apply p.val)
  map_add' p q := Subtype.ext
    ((PolynomialModule.equivPolynomial (R := R) (S := R)).symm.map_add p.val q.val)
  map_smul' a p := Subtype.ext
    ((PolynomialModule.equivPolynomial (R := R) (S := R)).symm.map_smul a p.val)

/-- The original Rees algebra is the direct sum of its actual ideal
powers, using the original polynomial coefficients. -/
def coefficientEquiv : ↥(reesAlgebra I) ≃ₗ[R] ⨁ n : ℕ, ↥(I ^ n) :=
  (polynomialModuleEquiv I).trans ((powerFiltration I).reesCoefficientEquiv)

/-- The constructed coefficient equivalence does not change a coefficient. -/
theorem coefficientEquiv_apply (p : ↥(reesAlgebra I)) (n : ℕ) :
    (coefficientEquiv I p n).val = p.val.coeff n := by
  have h := (powerFiltration I).reesCoefficientEquiv_apply (polynomialModuleEquiv I p) n
  exact congrArg Subtype.val h

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Tensoring the original Rees algebra separates it into the actual
tensor products with the original ideal powers. -/
def tensorCoefficientEquiv :
    ↥(reesAlgebra I) ⊗[R] M ≃ₗ[R] ⨁ n : ℕ, ↥(I ^ n) ⊗[R] M :=
  (TensorProduct.congr (coefficientEquiv I) (LinearEquiv.refl R M)).trans
    (TensorProduct.directSumLeft R R (fun n : ℕ => ↥(I ^ n)) M)

/-- On a pure tensor, each coefficient is its original polynomial
coefficient tensored with the original module element. -/
theorem tensorCoefficientEquiv_tmul (p : ↥(reesAlgebra I)) (x : M) (n : ℕ) :
    tensorCoefficientEquiv I M (p ⊗ₜ[R] x) n =
      (⟨p.val.coeff n, p.property n⟩ : ↥(I ^ n)) ⊗ₜ[R] x := by
  change TensorProduct.directSumLeft R R (fun n : ℕ => ↥(I ^ n)) M
    (TensorProduct.congr (coefficientEquiv I) (LinearEquiv.refl R M) (p ⊗ₜ[R] x)) n = _
  rw [TensorProduct.congr_tmul]
  have h := TensorProduct.directSumLeft_tmul R R (coefficientEquiv I p) x n
  exact h.trans (congrArg (fun a : ↥(I ^ n) => a ⊗ₜ[R] x)
    (Subtype.ext (coefficientEquiv_apply I p n)))

/-- Extraction of an actual tensor coefficient. -/
def coefficient (n : ℕ) : ↥(reesAlgebra I) ⊗[R] M →ₗ[R] ↥(I ^ n) ⊗[R] M :=
  (DirectSum.component R ℕ (fun n : ℕ => ↥(I ^ n) ⊗[R] M) n).comp
    (tensorCoefficientEquiv I M).toLinearMap

/-- Coefficient extraction retains the actual pure-tensor coefficient. -/
theorem coefficient_tmul (p : ↥(reesAlgebra I)) (x : M) (n : ℕ) :
    coefficient I M n (p ⊗ₜ[R] x) =
      (⟨p.val.coeff n, p.property n⟩ : ↥(I ^ n)) ⊗ₜ[R] x :=
  tensorCoefficientEquiv_tmul I M p x n

/-- Insertion of one homogeneous tensor coefficient in the original
tensor product with the Rees algebra. -/
def homogeneous (n : ℕ) : ↥(I ^ n) ⊗[R] M →ₗ[R] ↥(reesAlgebra I) ⊗[R] M :=
  (tensorCoefficientEquiv I M).symm.toLinearMap.comp
    (DirectSum.lof R ℕ (fun n : ℕ => ↥(I ^ n) ⊗[R] M) n)

/-- A homogeneous coefficient is recovered by extracting its own degree. -/
theorem coefficient_homogeneous (n : ℕ) (x : ↥(I ^ n) ⊗[R] M) :
    coefficient I M n (homogeneous I M n x) = x := by
  change (tensorCoefficientEquiv I M
    ((tensorCoefficientEquiv I M).symm
      (DirectSum.lof R ℕ (fun n : ℕ => ↥(I ^ n) ⊗[R] M) n x))) n = x
  rw [LinearEquiv.apply_symm_apply]
  exact DFinsupp.single_eq_same

/-- A homogeneous insertion has zero coefficient in every other degree. -/
theorem coefficient_homogeneous_ne (n k : ℕ) (h : k ≠ n) (x : ↥(I ^ n) ⊗[R] M) :
    coefficient I M k (homogeneous I M n x) = 0 := by
  change (tensorCoefficientEquiv I M
    ((tensorCoefficientEquiv I M).symm
      (DirectSum.lof R ℕ (fun n : ℕ => ↥(I ^ n) ⊗[R] M) n x))) k = 0
  rw [LinearEquiv.apply_symm_apply]
  exact DFinsupp.single_eq_of_ne h

/-- Equality of every actual tensor coefficient detects equality in
the original tensor product. -/
theorem ext_coefficients {x y : ↥(reesAlgebra I) ⊗[R] M}
    (h : ∀ n : ℕ, coefficient I M n x = coefficient I M n y) : x = y := by
  apply (tensorCoefficientEquiv I M).injective
  exact DFinsupp.ext h

end ReesTensorCoefficients
