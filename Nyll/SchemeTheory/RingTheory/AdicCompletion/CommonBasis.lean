/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Flat.LocalAdicBasis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Completion using one common family of basis representatives

Representatives of a residue basis in a flat module over a local ring give
one linear map from a free module. The map is an isomorphism modulo each
positive power of the maximal ideal. Its actual completed map is therefore
an isomorphism, even for an infinite residue basis.

The construction retains the original linear combination map. In particular,
it can transfer flatness of completed free modules to the completion of an
arbitrary flat module. This supplies the common-basis completion argument
used in Stacks, Tag 07QM, part (4).
-/

noncomputable section

open Module TensorProduct

universe u v w

namespace AdicCompletion

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- If a family becomes a basis after tensoring with a quotient ring,
its original linear combination map is an isomorphism modulo that ideal.
The comparison uses the actual tensor--quotient equivalences. -/
theorem linearCombination_reduceModIdeal_bijective
    (I : Ideal R) {ι : Type w} (x : ι → M)
    (b : Basis ι (R ⧸ I) ((R ⧸ I) ⊗[R] M))
    (hb : ∀ i, b i = 1 ⊗ₜ[R] x i) :
    Function.Bijective ((Finsupp.linearCombination R x).reduceModIdeal I) := by
  classical
  let A := R ⧸ I
  let F := ι →₀ R
  let f : F →ₗ[R] M := Finsupp.linearCombination R x
  let bF : Basis ι A (A ⊗[R] F) := (Finsupp.basisSingleOne : Basis ι R F).baseChange A
  let e : (A ⊗[R] F) ≃ₗ[A] (A ⊗[R] M) := bF.equiv b (Equiv.refl ι)
  have he : f.baseChange A = e.toLinearMap := by
    apply bF.ext
    intro i
    have he₀ : e (bF i) = b i := bF.equiv_apply i b (Equiv.refl ι)
    change f.baseChange A (bF i) = e (bF i)
    rw [he₀]
    change f.baseChange A (((Finsupp.basisSingleOne : Basis ι R F).baseChange A) i) = b i
    rw [Basis.baseChange_apply, Finsupp.coe_basisSingleOne, LinearMap.baseChange_tmul]
    change (1 : A) ⊗ₜ[R] Finsupp.linearCombination R x (Finsupp.single i 1) = b i
    rw [Finsupp.linearCombination_single, one_smul, hb i]
  have hf : Function.Bijective (f.baseChange A) := by
    rw [he]
    exact e.bijective
  let eF : (A ⊗[R] F) ≃ₗ[R] F ⧸ (I • (⊤ : Submodule R F)) :=
    TensorProduct.quotTensorEquivQuotSMul F I
  let eM : (A ⊗[R] M) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M I
  have hq : ∀ z : F ⧸ (I • (⊤ : Submodule R F)),
      f.reduceModIdeal I z = eM (f.baseChange A (eF.symm z)) := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R F)) z
    change Submodule.Quotient.mk (f z) =
      TensorProduct.quotTensorEquivQuotSMul M I
        (f.baseChange A ((TensorProduct.quotTensorEquivQuotSMul F I).symm
          (Submodule.Quotient.mk z)))
    rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearMap.baseChange_tmul,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  constructor
  · intro z z' h
    apply eF.symm.injective
    apply hf.1
    apply eM.injective
    rw [← hq z, ← hq z']
    exact h
  · intro z
    obtain ⟨y, hy⟩ := hf.2 (eM.symm z)
    refine ⟨eF y, ?_⟩
    change f.reduceModIdeal I (eF y) = z
    rw [hq, eF.symm_apply_apply, hy, eM.apply_symm_apply]

variable [IsLocalRing R] [Module.Flat R M]

/-- For prescribed representatives of a residue basis, completion of the
actual linear combination map is bijective. No finite rank or finite
generation hypothesis is required. -/
theorem map_linearCombination_bijective_of_residue_basis
    {ι : Type w} (x : ι → M)
    (b : Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M))
    (hb : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x i = b i) :
    Function.Bijective
      (AdicCompletion.map (IsLocalRing.maximalIdeal R) (Finsupp.linearCombination R x)) := by
  let I : Ideal R := IsLocalRing.maximalIdeal R
  let F := ι →₀ R
  let f : F →ₗ[R] M := Finsupp.linearCombination R x
  have hred : ∀ n, Function.Bijective (f.reduceModIdeal (I ^ (n + 1))) := by
    intro n
    obtain ⟨bₙ, hbₙ⟩ :=
      IsLocalRing.exists_basis_tensor_quotient_pow_of_residue_basis x b hb n
    exact linearCombination_reduceModIdeal_bijective (I ^ (n + 1)) x bₙ hbₙ
  constructor
  · intro z z' h
    apply AdicCompletion.ext
    intro n
    have hnext : z.val (n + 1) = z'.val (n + 1) := by
      apply (hred n).1
      exact congrArg (fun y : AdicCompletion I M => y.val (n + 1)) h
    calc
      z.val n = AdicCompletion.transitionMap I F (Nat.le_succ n) (z.val (n + 1)) :=
        (z.property (Nat.le_succ n)).symm
      _ = AdicCompletion.transitionMap I F (Nat.le_succ n) (z'.val (n + 1)) :=
        congrArg (AdicCompletion.transitionMap I F (Nat.le_succ n)) hnext
      _ = z'.val n := z'.property (Nat.le_succ n)
  · apply AdicCompletion.map_surjective_of_mkQ_comp_surjective
    have hredOne : Function.Surjective (f.reduceModIdeal I) := by
      have hpow : I ^ (0 + 1) = I := pow_one I
      exact hpow ▸ (hred 0).2
    intro z
    obtain ⟨y, hy⟩ := hredOne z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R F)) y
    refine ⟨y, ?_⟩
    exact hy

/-- The completion of an arbitrary flat module over a local ring is
isomorphic to the completion of a free module, through the completed map
of a single family of actual residue-basis representatives. -/
theorem exists_finsupp_completion_equiv_of_flat :
    ∃ (ι : Type (max u v)) (x : ι → M)
      (e : AdicCompletion (IsLocalRing.maximalIdeal R) (ι →₀ R)
        ≃ₗ[AdicCompletion (IsLocalRing.maximalIdeal R) R]
          AdicCompletion (IsLocalRing.maximalIdeal R) M),
      ∀ z, e z = AdicCompletion.map (IsLocalRing.maximalIdeal R)
        (Finsupp.linearCombination R x) z := by
  obtain ⟨ι, x, ⟨b, hb⟩, _⟩ :=
    IsLocalRing.exists_common_basis_tensor_quotient_pow (R := R) (M := M)
  have hf := map_linearCombination_bijective_of_residue_basis x b (fun i => (hb i).symm)
  exact ⟨ι, x, LinearEquiv.ofBijective
    (AdicCompletion.map (IsLocalRing.maximalIdeal R) (Finsupp.linearCombination R x)) hf,
    fun _ => rfl⟩

end AdicCompletion
