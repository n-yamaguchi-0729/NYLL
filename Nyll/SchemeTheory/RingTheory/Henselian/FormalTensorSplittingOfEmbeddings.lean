/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalSeparableTensorSplitting

/-! # Formal splitting over an actual splitting field

A complete finite family of residue embeddings lifts to a splitting over
power series over that same field. In particular the coefficient field can
be a Laurent field; algebraic closedness is unnecessary. The actual lifts
are the existing simple-root lifts. Their evaluation matrix has the given
residue evaluation matrix, whose nonzero determinant makes it invertible.
-/

noncomputable section

open scoped TensorProduct

namespace PowerSeries

/-- A finite separable extension with a complete family of actual residue
embeddings splits after an arbitrary deformation of its base. This retains
both the coefficient field and every labelled formal embedding. -/
theorem exists_formalTensorProductEquiv_of_embeddings
    {E F L : Type*} [Field E] [Field F] [Field L]
    [Algebra E F] [Algebra E L]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (n : ℕ) (hn : Module.finrank E F = n)
    (ι : Fin n → F →ₐ[E] L) (hι : Function.Injective ι)
    (τ : E →+* PowerSeries L)
    (hτ : constantCoeff.comp τ = algebraMap E L) :
    let algPS : Algebra E (PowerSeries L) := τ.toAlgebra
    let _ : Module E (PowerSeries L) := algPS.toModule
    ∃ split : (PowerSeries L ⊗[E] F) ≃ₐ[PowerSeries L]
        (Fin n → PowerSeries L),
      ∀ (a : PowerSeries L) (b : F) (j : Fin n),
        split (a ⊗ₜ[E] b) j = a * formalEmbeddingLift τ hτ (ι j) b := by
  classical
  intro algPS modPS
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  let index : Fin pb.dim ≃ Fin n := finCongr (pb.finrank.symm.trans hn)
  let φ (j : Fin n) : F →ₐ[E] PowerSeries L :=
    { toRingHom := formalEmbeddingLift τ hτ (ι j)
      commutes' := fun a => RingHom.congr_fun (formalEmbeddingLift_spec τ hτ (ι j)).1 a }
  let f : (PowerSeries L ⊗[E] F) →ₐ[PowerSeries L] (Fin n → PowerSeries L) :=
    AlgHom.pi fun j => AlgHom.liftEquiv E (PowerSeries L) F (PowerSeries L) (φ j)
  let fN : (PowerSeries L ⊗[E] F) →ₐ[PowerSeries L]
      (Fin pb.dim → PowerSeries L) :=
    AlgHom.pi fun j => AlgHom.liftEquiv E (PowerSeries L) F (PowerSeries L) (φ (index j))
  let b := pb.basis.baseChange (PowerSeries L)
  let c := Pi.basisFun (PowerSeries L) (Fin pb.dim)
  let M := LinearMap.toMatrix b c fN.toLinearMap
  have hmatrix : M = Matrix.vandermonde
      (fun j : Fin pb.dim => formalEmbeddingLift τ hτ (ι (index j)) pb.gen) := by
    apply Matrix.ext
    intro i j
    change LinearMap.toMatrix b c fN.toLinearMap i j = _
    rw [LinearMap.toMatrix_apply]
    simp only [c, Pi.basisFun_repr]
    change fN ((pb.basis.baseChange (PowerSeries L)) j) i =
      (formalEmbeddingLift τ hτ (ι (index i)) pb.gen) ^ (j : ℕ)
    rw [Module.Basis.baseChange_apply, PowerBasis.basis_eq_pow]
    change (AlgHom.liftEquiv E (PowerSeries L) F (PowerSeries L) (φ (index i)))
      ((1 : PowerSeries L) ⊗ₜ[E] (pb.gen ^ (j : ℕ))) = _
    rw [AlgHom.liftEquiv_tmul, one_smul]
    exact (φ (index i)).map_pow pb.gen (j : ℕ)
  have hresidue : M.map constantCoeff =
      Matrix.vandermonde (fun j : Fin pb.dim => ι (index j) pb.gen) := by
    rw [hmatrix]
    apply Matrix.ext
    intro i j
    change constantCoeff ((formalEmbeddingLift τ hτ (ι (index i)) pb.gen) ^ (j : ℕ)) =
      (ι (index i) pb.gen) ^ (j : ℕ)
    rw [map_pow]
    exact congrArg (fun z : L => z ^ (j : ℕ))
      (RingHom.congr_fun (formalEmbeddingLift_spec τ hτ (ι (index i))).2 pb.gen)
  have hdet : IsUnit M.det := by
    apply isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hresidue,
      Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact index.injective (hι (pb.algHom_ext hij))
  let eLin : (PowerSeries L ⊗[E] F) ≃ₗ[PowerSeries L]
      (Fin pb.dim → PowerSeries L) :=
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
  intro a b j
  exact AlgHom.liftEquiv_tmul (φ j) a b

end PowerSeries
