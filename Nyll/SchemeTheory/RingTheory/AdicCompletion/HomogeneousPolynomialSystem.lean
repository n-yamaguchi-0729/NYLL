/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientSequence
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Actual fixed-degree polynomials from compatible adic coefficients

For finitely many variables, there are only finitely many exponent
vectors of a fixed total degree. Lift every coefficient of a compatible
system by completeness of the original ring, and sum over that finite
set of exponent vectors. The resulting object is an actual homogeneous
polynomial over the original ring, and all its reductions are the given
polynomials. Separatedness proves uniqueness coefficient by coefficient.

The same construction recovers matrices entry by entry. No Noetherian
hypothesis, bounded support assumption beyond fixed degree, or given
algebraization of the polynomial system is needed.
-/

noncomputable section

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommRing R] (I : Ideal R)

private def idealPowerModuleQuotientEquiv (k : ℕ) :
    (R ⧸ I ^ (k + 1)) ≃ₗ[R] AdicModuleSystem.quotientSequenceModule I R k :=
  Submodule.quotEquivOfEq (I ^ (k + 1))
    (I ^ (k + 1) • (⊤ : Submodule R R))
    ((Ideal.smul_eq_mul (I ^ (k + 1)) ⊤).trans (Ideal.mul_top (I ^ (k + 1)))).symm

private theorem idealPowerModuleQuotientEquiv_mk (k : ℕ) (r : R) :
    idealPowerModuleQuotientEquiv I k (Ideal.Quotient.mk (I ^ (k + 1)) r) =
      Submodule.Quotient.mk r := rfl

private theorem idealPowerModuleQuotientEquiv_transition (k : ℕ)
    (x : R ⧸ I ^ ((k + 1) + 1)) :
    AdicModuleSystem.quotientSequenceTransition I R k
        (idealPowerModuleQuotientEquiv I (k + 1) x) =
      idealPowerModuleQuotientEquiv I k
        (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1)) x) := by
  exact Quotient.inductionOn' x (fun _ : R => rfl)

private def scalarQuotientSequence
    (x : (k : ℕ) → R ⧸ I ^ (k + 1))
    (hx : ∀ k : ℕ, Ideal.Quotient.factorPow I (Nat.le_succ (k + 1)) (x (k + 1)) = x k) :
    AdicModuleSystem.sections (fun k => AdicModuleSystem.quotientSequenceModule I R k)
      (AdicModuleSystem.quotientSequenceTransition I R) :=
  ⟨fun k => idealPowerModuleQuotientEquiv I k (x k), fun k =>
    (idealPowerModuleQuotientEquiv_transition I k (x (k + 1))).trans
      (congrArg (idealPowerModuleQuotientEquiv I k) (hx k))⟩

section CompleteScalars

variable [IsAdicComplete I R]

private def scalarQuotientLift
    (x : (k : ℕ) → R ⧸ I ^ (k + 1))
    (hx : ∀ k : ℕ, Ideal.Quotient.factorPow I (Nat.le_succ (k + 1)) (x (k + 1)) = x k) : R :=
  (AdicModuleSystem.quotientSequenceEquiv I R).symm (scalarQuotientSequence I x hx)

private theorem scalarQuotientLift_mk
    (x : (k : ℕ) → R ⧸ I ^ (k + 1))
    (hx : ∀ k : ℕ, Ideal.Quotient.factorPow I (Nat.le_succ (k + 1)) (x (k + 1)) = x k)
    (k : ℕ) :
    Ideal.Quotient.mk (I ^ (k + 1)) (scalarQuotientLift I x hx) = x k := by
  apply (idealPowerModuleQuotientEquiv I k).injective
  exact (idealPowerModuleQuotientEquiv_mk I k (scalarQuotientLift I x hx)).trans
    (AdicModuleSystem.quotientSequenceEquiv_symm_mk I R k (scalarQuotientSequence I x hx))

end CompleteScalars

variable {σ : Type v} [Finite σ]

private def homogeneousExponents (d : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_nat_weight_eq (1 : σ → ℕ) (fun _ => one_ne_zero) d).toFinset

private theorem mem_homogeneousExponents (d : ℕ) (e : σ →₀ ℕ) :
    e ∈ homogeneousExponents (σ := σ) d ↔ e.degree = d := by
  simp only [homogeneousExponents, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    Finsupp.degree_eq_weight_one]
  rfl

variable (d : ℕ)
  (p : (k : ℕ) → homogeneousSubmodule σ (R ⧸ I ^ (k + 1)) d)
  (hp : ∀ k : ℕ,
    map (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))) (p (k + 1)).val = (p k).val)

include hp

omit [Finite σ] in
private theorem coefficient_compatible (e : σ →₀ ℕ) (k : ℕ) :
    Ideal.Quotient.factorPow I (Nat.le_succ (k + 1)) ((p (k + 1)).val.coeff e) =
      (p k).val.coeff e := by
  have h := congrArg (fun q : MvPolynomial σ (R ⧸ I ^ (k + 1)) => q.coeff e) (hp k)
  exact (coeff_map _ _ e).symm.trans h

variable [IsAdicComplete I R]

/-- Lift the original coefficients and sum the actual finitely many
monomials of degree `d`. -/
def homogeneousAdicLift : homogeneousSubmodule σ R d := by
  classical
  let c : (σ →₀ ℕ) → R := fun e => scalarQuotientLift I
    (fun k => (p k).val.coeff e) (coefficient_compatible I d p hp e)
  refine ⟨∑ e ∈ homogeneousExponents (σ := σ) d, monomial e (c e), ?_⟩
  apply IsHomogeneous.sum
  intro e he
  exact isHomogeneous_monomial (c e) ((mem_homogeneousExponents d e).mp he)

/-- The actual homogeneous lift reduces to the original polynomial
at every supplied positive adic degree. -/
theorem homogeneousAdicLift_map (k : ℕ) :
    map (Ideal.Quotient.mk (I ^ (k + 1))) (homogeneousAdicLift I d p hp).val = (p k).val := by
  classical
  let S : Finset (σ →₀ ℕ) := homogeneousExponents d
  let c : (σ →₀ ℕ) → R := fun e => scalarQuotientLift I
    (fun k => (p k).val.coeff e) (coefficient_compatible I d p hp e)
  have hsupport : (p k).val.support ⊆ S := by
    intro e he
    apply (mem_homogeneousExponents d e).mpr
    rw [Finsupp.degree_eq_weight_one]
    exact (p k).property (MvPolynomial.mem_support_iff.mp he)
  calc
    map (Ideal.Quotient.mk (I ^ (k + 1))) (∑ e ∈ S, monomial e (c e)) =
        ∑ e ∈ S, monomial e ((p k).val.coeff e) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [map_monomial]
      exact congrArg (monomial e)
        (scalarQuotientLift_mk I (fun k => (p k).val.coeff e)
          (coefficient_compatible I d p hp e) k)
    _ = ∑ e ∈ (p k).val.support, monomial e ((p k).val.coeff e) := by
      symm
      apply Finset.sum_subset hsupport
      intro e _ he
      rw [MvPolynomial.notMem_support_iff.mp he, monomial_zero]
    _ = (p k).val := support_sum_monomial_coeff (p k).val

/-- Separatedness gives uniqueness of the actual fixed-degree lift. -/
theorem homogeneousAdicLift_unique (q : homogeneousSubmodule σ R d)
    (hq : ∀ k : ℕ, map (Ideal.Quotient.mk (I ^ (k + 1))) q.val = (p k).val) :
    q = homogeneousAdicLift I d p hp := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro e
  have h : (fun _ : Unit => q.val.coeff e) =
      fun _ : Unit => (homogeneousAdicLift I d p hp).val.coeff e := by
    apply IsHausdorff.StrictMono.funext' I (strictMono_id.add_const 1)
    intro k _
    have he := congrArg (fun r : MvPolynomial σ (R ⧸ I ^ (k + 1)) => r.coeff e)
      ((hq k).trans (homogeneousAdicLift_map I d p hp k).symm)
    exact (coeff_map _ _ e).symm.trans (he.trans (coeff_map _ _ e))
  exact congrFun h ()

/-- Every compatible fixed-degree homogeneous polynomial system has
one and only one actual lift over the complete coefficient ring. -/
theorem existsUnique_homogeneous_adic_lift :
    ∃! q : homogeneousSubmodule σ R d,
      ∀ k : ℕ, map (Ideal.Quotient.mk (I ^ (k + 1))) q.val = (p k).val :=
  ⟨homogeneousAdicLift I d p hp, homogeneousAdicLift_map I d p hp,
    fun q hq => homogeneousAdicLift_unique I d p hp q hq⟩

omit p hp in
/-- A compatible homogeneous polynomial matrix is the reduction of
exactly one actual matrix over the complete coefficient ring. -/
theorem existsUnique_homogeneous_adic_matrix_lift (α β : Type w)
    (m : (k : ℕ) → α → β → homogeneousSubmodule σ (R ⧸ I ^ (k + 1)) d)
    (hm : ∀ (k : ℕ) (a : α) (b : β),
      map (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))) (m (k + 1) a b).val =
        (m k a b).val) :
    ∃! q : α → β → homogeneousSubmodule σ R d,
      ∀ (k : ℕ) (a : α) (b : β),
        map (Ideal.Quotient.mk (I ^ (k + 1))) (q a b).val = (m k a b).val := by
  let q : α → β → homogeneousSubmodule σ R d := fun a b =>
    homogeneousAdicLift I d (fun k => m k a b) (fun k => hm k a b)
  refine ⟨q, ?_, ?_⟩
  · intro k a b
    exact homogeneousAdicLift_map I d (fun k => m k a b) (fun k => hm k a b) k
  · intro r hr
    funext a b
    exact homogeneousAdicLift_unique I d (fun k => m k a b) (fun k => hm k a b)
      (r a b) (fun k => hr k a b)

end MvPolynomial
