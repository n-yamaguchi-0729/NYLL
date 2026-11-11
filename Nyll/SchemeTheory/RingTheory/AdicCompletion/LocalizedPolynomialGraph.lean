/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.PolynomialLocalizationDerivation
public import Nyll.SchemeTheory.RingTheory.Derivation.TensorProduct
public import Nyll.SchemeTheory.RingTheory.Polynomial.TensorGraph
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The actual Jacobian of completed localized polynomial graph relations

The original polynomial partial derivatives, extended first to the local
ring at the specified prime and then to its adic completion, act on the
left factor of the integer tensor product. Their values on the coordinate
graph relations are Kronecker deltas. For finitely many variables, the
resulting determinant is literally one.

The right coefficient ring may have arbitrary characteristic. No ambient
regularity or geometric regularity of the formal fibre is assumed here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {σ : Type*} (p : Ideal (MvPolynomial σ ℤ)) [p.IsPrime]
  (A : Type*) [CommRing A] [Algebra (MvPolynomial σ ℤ) A]
  [IsLocalization p.primeCompl A] (I : Ideal A) (B : Type*) [CommRing B]

/-- Apply the actual completed localized partial derivative to the left
tensor factor while fixing the right coefficient ring. -/
def pderivLocalizedAdicTensor (i : σ) :
    Derivation ℤ (AdicCompletion I A ⊗[ℤ] B)
      (AdicCompletion I A ⊗[ℤ] B) :=
  (pderivLocalizedAdicCompletion p A I i).tensorLeft B

/-- The actual coordinate graph has the identity derivative matrix in
the completed polynomial localization tensored with the coefficient ring. -/
theorem pderivLocalizedAdicTensor_graph [DecidableEq σ] (b : σ → B) (i j : σ) :
    pderivLocalizedAdicTensor p A I B i
      (Algebra.TensorProduct.polynomialGraphRelation σ
        (AdicCompletion I A) B b j) =
      if i = j then 1 else 0 := by
  change (pderivLocalizedAdicCompletion p A I i).tensorLeft B
    (algebraMap (MvPolynomial σ ℤ) (AdicCompletion I A)
      (X j) ⊗ₜ[ℤ] (1 : B) - 1 ⊗ₜ[ℤ] b j) = _
  rw [map_sub, Derivation.tensorLeft_tmul, Derivation.tensorLeft_tmul,
    Derivation.map_one_eq_zero, TensorProduct.zero_tmul, sub_zero,
    pderivLocalizedAdicCompletion_X]
  by_cases h : i = j
  · rw [ite_eq_left h, ← Algebra.TensorProduct.one_def, ite_eq_left h]
  · rw [ite_eq_right h, TensorProduct.zero_tmul, ite_eq_right h]

/-- For finitely many coordinates the constructed Jacobian determinant
is one, giving its unit witness without a Jacobian assumption. -/
theorem det_pderivLocalizedAdicTensor_graph [Fintype σ] [DecidableEq σ] (b : σ → B) :
    Matrix.det (fun i j : σ => pderivLocalizedAdicTensor p A I B i
      (Algebra.TensorProduct.polynomialGraphRelation σ
        (AdicCompletion I A) B b j)) = 1 := by
  have hmatrix :
      (fun i j : σ => pderivLocalizedAdicTensor p A I B i
        (Algebra.TensorProduct.polynomialGraphRelation σ
          (AdicCompletion I A) B b j)) =
      (1 : Matrix σ σ (AdicCompletion I A ⊗[ℤ] B)) := by
    ext i j
    exact (pderivLocalizedAdicTensor_graph p A I B b i j).trans Matrix.one_apply.symm
  rw [hmatrix, Matrix.det_one]

end MvPolynomial
