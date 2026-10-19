/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Tensor products and actual ideal-power reductions

Moving the scalar quotient through the tensor factors gives an explicit
comparison between tensoring a reduced module and reducing the tensor
product. Neither tensor factor is assumed flat. The comparison sends the
original pure tensor to the class of that same pure tensor. This explicit
formula supplies the comparison needed for maps of the original factors.
-/

noncomputable section

open scoped TensorProduct

namespace TensorProduct

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

/-- Tensoring an ideal quotient is the actual ideal quotient of the tensor product. -/
def tensorIdealQuotientEquiv :
    M ⊗[R] (N ⧸ (I • (⊤ : Submodule R N))) ≃ₗ[R]
      (M ⊗[R] N) ⧸ (I • (⊤ : Submodule R (M ⊗[R] N))) :=
  (TensorProduct.congr (LinearEquiv.refl R M) (quotTensorEquivQuotSMul N I).symm).trans
    ((TensorProduct.assoc R M (R ⧸ I) N).symm.trans
      ((TensorProduct.congr (TensorProduct.comm R M (R ⧸ I)) (LinearEquiv.refl R N)).trans
        ((TensorProduct.assoc R (R ⧸ I) M N).trans
          (quotTensorEquivQuotSMul (M ⊗[R] N) I))))

/-- The comparison retains the original tensor factors. -/
theorem tensorIdealQuotientEquiv_tmul_mk (x : M) (y : N) :
    tensorIdealQuotientEquiv I M N (x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) := by
  simp only [tensorIdealQuotientEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, quotTensorEquivQuotSMul_symm_mk, TensorProduct.assoc_symm_tmul,
    TensorProduct.comm_tmul, TensorProduct.assoc_tmul, quotTensorEquivQuotSMul_mk_one_tmul]

/-- The inverse comparison also preserves the original representative. -/
theorem tensorIdealQuotientEquiv_symm_mk_tmul (x : M) (y : N) :
    (tensorIdealQuotientEquiv I M N).symm (Submodule.Quotient.mk (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] Submodule.Quotient.mk y := by
  apply (tensorIdealQuotientEquiv I M N).injective
  rw [LinearEquiv.apply_symm_apply, tensorIdealQuotientEquiv_tmul_mk]

end TensorProduct
