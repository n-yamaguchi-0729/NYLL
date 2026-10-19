/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Flat.NilpotentFlatBasis
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# A common basis for the infinitesimal fibres of a flat local module

Choose representatives of a basis of the closed fibre of a flat module.
The same representatives give bases after reduction modulo every positive
power of the maximal ideal. This follows by lifting the residue basis over
each quotient ring, whose maximal ideal is nilpotent. In particular, the
bases in different degrees are obtained from one family in the original
module, rather than by independent choices in its quotients.

This is the module-theoretic input of Stacks, Tag 07QM, part (4), without a
finiteness assumption on the module or its closed fibre.
-/

noncomputable section

open Module TensorProduct

universe u v w

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

/-- A prescribed residue basis remains a basis in each positive adic
quotient, after using the same representatives in the original module. -/
theorem exists_basis_tensor_quotient_pow_of_residue_basis
    {ι : Type w} (x : ι → M)
    (b : Basis ι (ResidueField R) (ResidueField R ⊗[R] M))
    (hb : ∀ i, (1 : ResidueField R) ⊗ₜ[R] x i = b i) (n : ℕ) :
    ∃ bₙ : Basis ι (R ⧸ maximalIdeal R ^ (n + 1))
        ((R ⧸ maximalIdeal R ^ (n + 1)) ⊗[R] M),
      ∀ i, bₙ i = 1 ⊗ₜ[R] x i := by
  let I : Ideal R := maximalIdeal R ^ (n + 1)
  let A := R ⧸ I
  have hI : I ≠ ⊤ := by
    intro h
    rcases Ideal.pow_eq_top_iff.mp h with hmax | hn
    · exact (maximalIdeal.isMaximal R).ne_top hmax
    · exact Nat.succ_ne_zero n hn
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap R A) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hNil : IsNilpotent (maximalIdeal A) := by
    refine ⟨n + 1, ?_⟩
    change maximalIdeal A ^ (n + 1) = ⊥
    rw [← map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  let k := ResidueField R
  let K := ResidueField A
  let Q := A ⊗[R] M
  let e : K ⊗[k] (k ⊗[R] M) ≃ₗ[K] K ⊗[A] Q :=
    AlgebraTensorModule.cancelBaseChange R k K K M ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R A K K M).symm
  let bK : Basis ι K (K ⊗[A] Q) := (b.baseChange K).map e
  have hbK : ∀ i, (1 : K) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] x i) = bK i := by
    intro i
    change (1 : K) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] x i) =
      (AlgebraTensorModule.cancelBaseChange R A K K M).symm
        (AlgebraTensorModule.cancelBaseChange R k K K M ((b.baseChange K) i))
    rw [Basis.baseChange_apply, ← hb i,
      AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      AlgebraTensorModule.cancelBaseChange_symm_tmul]
  exact exists_basis_of_flat_of_isNilpotent_maximalIdeal
    (R := A) (M := Q) hNil (fun i => (1 : A) ⊗ₜ[R] x i) bK hbK

/-- A single family in a flat module gives bases in all of its positive
adic quotients. The family is constructed by lifting a vector-space basis
of the actual closed fibre. -/
theorem exists_common_basis_tensor_quotient_pow :
    ∃ (ι : Type (max u v)) (x : ι → M),
      (∃ b : Basis ι (ResidueField R) (ResidueField R ⊗[R] M),
        ∀ i, b i = 1 ⊗ₜ[R] x i) ∧
      ∀ n : ℕ, ∃ bₙ : Basis ι (R ⧸ maximalIdeal R ^ (n + 1))
          ((R ⧸ maximalIdeal R ^ (n + 1)) ⊗[R] M),
        ∀ i, bₙ i = 1 ⊗ₜ[R] x i := by
  let b := Module.Free.chooseBasis (ResidueField R) (ResidueField R ⊗[R] M)
  obtain ⟨x, hx⟩ :=
    (TensorProduct.mk_surjective R M (ResidueField R) Ideal.Quotient.mk_surjective).comp_left b
  refine ⟨Module.Free.ChooseBasisIndex (ResidueField R) (ResidueField R ⊗[R] M),
    x, ⟨b, fun i => (congrFun hx i).symm⟩, ?_⟩
  intro n
  exact exists_basis_tensor_quotient_pow_of_residue_basis x b (fun i => congrFun hx i) n

end IsLocalRing
