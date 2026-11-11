/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Coefficient Frobenius on affine coordinate rings

For every positive power of arithmetic Frobenius, its difference from the
identity is surjective on a scalar extension from a finite field to an
algebraic closure. This is coefficient Frobenius, not absolute Frobenius
on the coordinate ring. The result descends to the actual additive
Artin–Schreier quotient of that ring.

The comparison with étale cyclic characters, and the extension to higher
prime-power characters, are separate from this algebraic statement.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace FiniteField

variable (k Ω : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]

/-- Every positive arithmetic Frobenius difference is surjective on the
algebraic closure of the finite constant field. -/
theorem frobenius_pow_sub_id_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x : Ω => (frobeniusAlgEquivOfAlgebraic k Ω ^ n) x - x) := by
  have hdegree : (Polynomial.X ^ (Fintype.card k ^ n) - Polynomial.X :
      Polynomial Ω).natDegree ≠ 0 := by
    rw [X_pow_card_sub_X_natDegree_eq Ω (one_lt_pow₀ Fintype.one_lt_card hn)]
    exact pow_ne_zero _ Fintype.card_ne_zero
  intro a
  obtain ⟨x, hx⟩ := IsAlgClosed.eval_surjective hdegree a
  refine ⟨x, ?_⟩
  rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] using hx

variable (M : Type*) [AddCommGroup M] [Module k M]

/-- Coefficient Frobenius minus the identity is surjective after any scalar
extension of a vector space; finite dimensionality is unnecessary. -/
theorem coefficientFrobenius_sub_id_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x : M ⊗[k] Ω =>
      ((frobeniusAlgEquivOfAlgebraic k Ω ^ n).toLinearMap.lTensor M) x - x) := by
  have h := LinearMap.lTensor_surjective M
    (g := (frobeniusAlgEquivOfAlgebraic k Ω ^ n).toLinearMap - LinearMap.id)
    (frobenius_pow_sub_id_surjective k Ω n hn)
  intro y
  obtain ⟨x, hx⟩ := h y
  refine ⟨x, ?_⟩
  simpa only [LinearMap.lTensor_sub, LinearMap.lTensor_id,
    LinearMap.sub_apply, LinearMap.id_apply] using hx

variable (R : Type*) [CommRing R] [Algebra k R]

/-- Arithmetic Frobenius acts on the constants and fixes the original
coordinate ring. -/
def coefficientFrobenius (n : ℕ) : R ⊗[k] Ω →ₐ[k] R ⊗[k] Ω :=
  Algebra.TensorProduct.map (AlgHom.id k R)
    (frobeniusAlgEquivOfAlgebraic k Ω ^ n).toAlgHom

omit [IsAlgClosed Ω] in
theorem coefficientFrobenius_tmul (n : ℕ) (r : R) (a : Ω) :
    coefficientFrobenius k Ω R n (r ⊗ₜ[k] a) =
      r ⊗ₜ[k] (frobeniusAlgEquivOfAlgebraic k Ω ^ n) a := rfl

variable (p : ℕ) [Fact p.Prime] [CharP (R ⊗[k] Ω) p]

/-- The action induced by coefficient Frobenius on the actual
Artin–Schreier classes of the scalar-extended coordinate ring. -/
def coefficientFrobeniusArtinSchreier (n : ℕ) :
    (R ⊗[k] Ω) ⧸ ((frobenius (R ⊗[k] Ω) p).toAddMonoidHom -
      AddMonoidHom.id (R ⊗[k] Ω)).range →+
    (R ⊗[k] Ω) ⧸ ((frobenius (R ⊗[k] Ω) p).toAddMonoidHom -
      AddMonoidHom.id (R ⊗[k] Ω)).range :=
  QuotientAddGroup.map _ _ (coefficientFrobenius k Ω R n).toAddMonoidHom (by
    rintro a ⟨b, rfl⟩
    refine ⟨coefficientFrobenius k Ω R n b, ?_⟩
    change (coefficientFrobenius k Ω R n b) ^ p - coefficientFrobenius k Ω R n b =
      coefficientFrobenius k Ω R n (b ^ p - b)
    rw [map_sub, map_pow])

/-- There are no coefficient-Frobenius coinvariants in the additive
Artin–Schreier classes, for any positive Frobenius power. -/
theorem coefficientFrobeniusArtinSchreier_sub_id_surjective
    (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x => coefficientFrobeniusArtinSchreier k Ω R p n x - x) := by
  let N := ((frobenius (R ⊗[k] Ω) p).toAddMonoidHom -
    AddMonoidHom.id (R ⊗[k] Ω)).range
  intro a
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective N a
  obtain ⟨b, hb⟩ := coefficientFrobenius_sub_id_surjective k Ω R n hn r
  refine ⟨QuotientAddGroup.mk' N b, ?_⟩
  change QuotientAddGroup.mk' N (coefficientFrobenius k Ω R n b) -
    QuotientAddGroup.mk' N b = QuotientAddGroup.mk' N r
  rw [← map_sub]
  exact congrArg (QuotientAddGroup.mk' N) hb

end FiniteField
