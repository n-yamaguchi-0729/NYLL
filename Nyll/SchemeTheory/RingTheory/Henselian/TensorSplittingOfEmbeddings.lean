/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor splitting by a complete family of actual embeddings

Evaluation in `n` distinct embeddings of a separable extension of degree `n`
is an algebra equivalence. The target field need not be algebraically closed.
-/

noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Distinct actual embeddings, as many as the extension degree, split the
scalar extension. The equivalence retains the labelled tensor formula. -/
theorem exists_equiv_pi_of_embeddings
    {E F L : Type*} [Field E] [Field F] [Field L]
    [Algebra E F] [Algebra E L] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (n : ℕ) (hn : Module.finrank E F = n)
    (ι : Fin n → F →ₐ[E] L) (hι : Function.Injective ι) :
    ∃ e : (L ⊗[E] F) ≃ₐ[L] (Fin n → L),
      ∀ a x j, e (a ⊗ₜ[E] x) j = a * ι j x := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  let index : Fin pb.dim ≃ Fin n := finCongr (pb.finrank.symm.trans hn)
  let f : (L ⊗[E] F) →ₐ[L] (Fin n → L) :=
    AlgHom.pi fun j => AlgHom.liftEquiv E L F L (ι j)
  let fN : (L ⊗[E] F) →ₐ[L] (Fin pb.dim → L) :=
    AlgHom.pi fun j => AlgHom.liftEquiv E L F L (ι (index j))
  let b := pb.basis.baseChange L
  let c := Pi.basisFun L (Fin pb.dim)
  let M := LinearMap.toMatrix b c fN.toLinearMap
  have hmatrix : M = Matrix.vandermonde (fun j : Fin pb.dim => ι (index j) pb.gen) := by
    apply Matrix.ext
    intro i j
    change LinearMap.toMatrix b c fN.toLinearMap i j = _
    rw [LinearMap.toMatrix_apply]
    simp only [c, Pi.basisFun_repr]
    change fN ((pb.basis.baseChange L) j) i = (ι (index i) pb.gen) ^ (j : ℕ)
    rw [Module.Basis.baseChange_apply, PowerBasis.basis_eq_pow]
    change (AlgHom.liftEquiv E L F L (ι (index i)))
      ((1 : L) ⊗ₜ[E] (pb.gen ^ (j : ℕ))) = _
    rw [AlgHom.liftEquiv_tmul, one_smul]
    exact (ι (index i)).map_pow pb.gen (j : ℕ)
  have hdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hmatrix, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact index.injective (hι (pb.algHom_ext hij))
  let eLin : (L ⊗[E] F) ≃ₗ[L] (Fin pb.dim → L) :=
    Matrix.toLinOfInv b c (Matrix.mul_nonsing_inv M hdet) (Matrix.nonsing_inv_mul M hdet)
  have hlin : eLin.toLinearMap = fN.toLinearMap := by
    change Matrix.toLin b c M = fN.toLinearMap
    exact Matrix.toLin_toMatrix b c fN.toLinearMap
  have hfN : Function.Bijective fN := by
    change Function.Bijective fN.toLinearMap
    rw [← hlin]
    exact eLin.bijective
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hfN.injective
      funext i
      exact congrFun hab (index i)
    · intro y
      obtain ⟨a, ha⟩ := hfN.surjective (fun i => y (index i))
      refine ⟨a, ?_⟩
      funext j
      have h := congrFun ha (index.symm j)
      change f a (index (index.symm j)) = y (index (index.symm j)) at h
      simpa only [Equiv.apply_symm_apply] using h
  refine ⟨AlgEquiv.ofBijective f hf, ?_⟩
  intro a x j
  exact AlgHom.liftEquiv_tmul (ι j) a x

end Algebra.TensorProduct
