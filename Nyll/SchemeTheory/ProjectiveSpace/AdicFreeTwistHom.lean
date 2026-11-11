/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
public import Nyll.SchemeTheory.ProjectiveSpace.PolynomialHomPullback
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.HomogeneousPolynomialSystem
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Recovery of compatible native free-to-twist morphisms

Consider original native sheaf morphisms from a fixed free sheaf to
a fixed finite free twist over every positive adic quotient. Their
compatibility is expressed by the actual transported scheme pullback.
The proved coefficient calculation turns that compatibility into
compatibility of their original homogeneous polynomial entries.

Completeness then constructs one native morphism over the original
ring. Its actual reduction is the given morphism at every stage, and
separatedness proves uniqueness. No compatible polynomial matrices or
lifted morphism are included as extra assumptions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original ideal defining a positive adic stage, shared by the native
morphism family and its quotient comparisons. -/
def adicFreeTwistHomStageIdeal (R : Type u) [CommRing R] (a : Ideal R) (k : ℕ) :
    Ideal R :=
  a ^ (k + 1)

variable (R : Type u) [CommRing R] (a : Ideal R) (n : ℕ)
  (I J : Type u) [Finite J] (d : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Compatible families of the actual native morphisms, using the
original coefficient quotient maps and actual transported pullbacks. -/
def adicFreeTwistHomSections : Type u :=
  { φ : (k : ℕ) → FreeTwistHom (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d // ∀ k : ℕ,
      freeTwistHomPullback (R ⧸ adicFreeTwistHomStageIdeal R a (k + 1))
        (R ⧸ adicFreeTwistHomStageIdeal R a k)
        (Ideal.Quotient.factorPow a (Nat.le_succ (k + 1))) n I J d (φ (k + 1)) = φ k }

/-- The actual reductions of a native morphism form a compatible
family under the original transition pullbacks. -/
def adicFreeTwistHomReduction (φ : FreeTwistHom R n I J d) :
    adicFreeTwistHomSections R a n I J d := by
  refine ⟨fun k =>
    freeTwistHomPullback R (R ⧸ adicFreeTwistHomStageIdeal R a k)
      (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k)) n I J d φ, ?_⟩
  intro k
  have hcomp := freeTwistHomPullback_comp R (R ⧸ adicFreeTwistHomStageIdeal R a (k + 1))
    (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a (k + 1))) n I J d
    (R ⧸ adicFreeTwistHomStageIdeal R a k)
    (Ideal.Quotient.factorPow a (Nat.le_succ (k + 1))) φ
  have hmk : (Ideal.Quotient.factorPow a (Nat.le_succ (k + 1))).comp
      (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a (k + 1))) =
        Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k) :=
    Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))
  exact hcomp.trans (congrArg (fun g : R →+* (R ⧸ adicFreeTwistHomStageIdeal R a k) =>
    freeTwistHomPullback R (R ⧸ adicFreeTwistHomStageIdeal R a k) g n I J d φ) hmk)

/-- Matrix entries of compatible native morphisms respect the coefficient quotient maps. -/
theorem adicFreeTwistHom_entries_compatible
    (φ : adicFreeTwistHomSections R a n I J d) (i : I) (j : J) (k : ℕ) :
    MvPolynomial.map (Ideal.Quotient.factorPow a (Nat.le_succ (k + 1)))
        ((freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a (k + 1))
          n I J d (φ.val (k + 1)) i j).val) =
      (freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k)
        n I J d (φ.val k) i j).val := by
  have he := freeTwistHomPullback_entry (R ⧸ adicFreeTwistHomStageIdeal R a (k + 1))
    (R ⧸ adicFreeTwistHomStageIdeal R a k)
    (Ideal.Quotient.factorPow a (Nat.le_succ (k + 1))) n I J d (φ.val (k + 1)) i j
  have hφ := congrArg (fun ψ : FreeTwistHom (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d =>
    (freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k)
      n I J d ψ i j).val) (φ.property k)
  exact he.symm.trans hφ

variable [IsAdicComplete a R]

/-- The homogeneous polynomial matrix lifted from compatible native morphisms. -/
def adicFreeTwistHomMatrix (φ : adicFreeTwistHomSections R a n I J d) :
    I → J → 𝒜 d := fun i j =>
  MvPolynomial.homogeneousAdicLift a d
    (fun k => freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k)
      n I J d (φ.val k) i j)
    (adicFreeTwistHom_entries_compatible R a n I J d φ i j)

/-- Construct the native morphism over the complete coefficient ring
from the original compatible sheaf morphisms. -/
def adicFreeTwistHomLift (φ : adicFreeTwistHomSections R a n I J d) : FreeTwistHom R n I J d :=
  polynomialMatrixHom R n I J d (adicFreeTwistHomMatrix R a n I J d φ)

/-- The constructed native morphism has exactly the original stage
morphism as its actual transported reduction. -/
theorem adicFreeTwistHomLift_reduction (φ : adicFreeTwistHomSections R a n I J d) (k : ℕ) :
    freeTwistHomPullback R (R ⧸ adicFreeTwistHomStageIdeal R a k)
        (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k)) n I J d
        (adicFreeTwistHomLift R a n I J d φ) = φ.val k := by
  apply (freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d).injective
  funext i j
  apply Subtype.ext
  have he := freeTwistHomPullback_entry R (R ⧸ adicFreeTwistHomStageIdeal R a k)
    (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k))
    n I J d (adicFreeTwistHomLift R a n I J d φ) i j
  have hm := congrArg Subtype.val (congrFun (congrFun
    (polynomialMatrixHom_matrix R n I J d (adicFreeTwistHomMatrix R a n I J d φ)) i) j)
  have hl := MvPolynomial.homogeneousAdicLift_map a d
    (fun k => freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k)
      n I J d (φ.val k) i j)
    (adicFreeTwistHom_entries_compatible R a n I J d φ i j) k
  have hc := congrArg (MvPolynomial.map (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k))) hm
  exact he.trans (hc.trans hl)

/-- Separatedness of coefficients makes the actual native lift unique. -/
theorem adicFreeTwistHomLift_unique (φ : adicFreeTwistHomSections R a n I J d)
    (ψ : FreeTwistHom R n I J d)
    (hψ : ∀ k : ℕ,
      freeTwistHomPullback R (R ⧸ adicFreeTwistHomStageIdeal R a k)
        (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k)) n I J d ψ = φ.val k) :
    ψ = adicFreeTwistHomLift R a n I J d φ := by
  apply (freeTwistPolynomialMatrixEquiv R n I J d).injective
  funext i j
  have hcoeff : ∀ k : ℕ,
      MvPolynomial.map (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k))
          (freeTwistPolynomialMatrixEquiv R n I J d ψ i j).val =
        (freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k)
          n I J d (φ.val k) i j).val := by
    intro k
    have he := freeTwistHomPullback_entry R (R ⧸ adicFreeTwistHomStageIdeal R a k)
      (Ideal.Quotient.mk (adicFreeTwistHomStageIdeal R a k))
      n I J d ψ i j
    exact he.symm.trans (congrArg
      (fun γ : FreeTwistHom (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d =>
        (freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k)
          n I J d γ i j).val) (hψ k))
  have hu := MvPolynomial.homogeneousAdicLift_unique a d
    (fun k => freeTwistPolynomialMatrixEquiv (R ⧸ adicFreeTwistHomStageIdeal R a k)
      n I J d (φ.val k) i j)
    (adicFreeTwistHom_entries_compatible R a n I J d φ i j)
    (freeTwistPolynomialMatrixEquiv R n I J d ψ i j) hcoeff
  exact hu.trans (congrFun (congrFun
    (polynomialMatrixHom_matrix R n I J d (adicFreeTwistHomMatrix R a n I J d φ)) i) j).symm

/-- Actual native morphisms between these fixed free twists are
equivalent to their compatible original adic reductions. -/
def adicFreeTwistHomEquiv : FreeTwistHom R n I J d ≃ adicFreeTwistHomSections R a n I J d where
  toFun := adicFreeTwistHomReduction R a n I J d
  invFun := adicFreeTwistHomLift R a n I J d
  left_inv φ := (adicFreeTwistHomLift_unique R a n I J d
    (adicFreeTwistHomReduction R a n I J d φ) φ (fun _ => rfl)).symm
  right_inv φ := Subtype.ext (funext (adicFreeTwistHomLift_reduction R a n I J d φ))

end AlgebraicGeometry.ProjSpace
