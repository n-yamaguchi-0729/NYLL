/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientRingComparison
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The closed formal fibre after extending its residue field

The existing evaluation equivalence for ideal-power quotients identifies
the base change of an adic completion to the original quotient with that
quotient. Tensor associativity then supplies the same identification after
any further scalar extension.

For the maximal ideal of a noetherian local ring, every field extension of
the residue field therefore gives a regular closed formal fibre. No
regularity assertion about the other formal fibres is used or claimed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The actual quotient base change of the completion is the original
quotient, with its native quotient-algebra structure. -/
def quotientBaseChangeAlgEquiv (I : Ideal R) (hI : I.FG) :
    ((R ⧸ I) ⊗[R] AdicCompletion I R) ≃ₐ[R ⧸ I] R ⧸ I := by
  let e :
      (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃ₐ[R]
        R ⧸ I :=
    (Ideal.quotientEquivAlgOfEq R
      (pow_one (I.map (algebraMap R (AdicCompletion I R)))).symm).trans
      ((quotientPowAlgEquiv I hI 1).trans
        (Ideal.quotientEquivAlgOfEq R (pow_one I)))
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
    (AdicCompletion I R) I).symm.trans
      (AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e)

/-- Extending the quotient coefficients keeps the same concrete
completion fibre. -/
def quotientAlgebraBaseChangeAlgEquiv (I : Ideal R) (hI : I.FG)
    (L : Type v) [CommRing L] [Algebra R L] [Algebra (R ⧸ I) L]
    [IsScalarTower R (R ⧸ I) L] :
    (L ⊗[R] AdicCompletion I R) ≃ₐ[L] L :=
  (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) L L
    (AdicCompletion I R)).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
        (quotientBaseChangeAlgEquiv I hI)).trans
          (Algebra.TensorProduct.rid (R ⧸ I) L L))

/-- Every field extension of the closed residue field gives a regular
base change of the maximal-adic completion. No finiteness or separability
of this field extension is required. -/
theorem closedFormalFiber_isRegularRing (R : Type u) (L : Type v)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field L] [Algebra R L] [Algebra (IsLocalRing.ResidueField R) L]
    [IsScalarTower R (IsLocalRing.ResidueField R) L] :
    IsRegularRing (AdicCompletion (IsLocalRing.maximalIdeal R) R ⊗[R] L) := by
  let quotientAlgebra : Algebra (R ⧸ IsLocalRing.maximalIdeal R) L :=
    ‹Algebra (IsLocalRing.ResidueField R) L›
  have quotientTower : IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) L :=
    ‹IsScalarTower R (IsLocalRing.ResidueField R) L›
  let e :
      (L ⊗[R] AdicCompletion (IsLocalRing.maximalIdeal R) R) ≃ₐ[L] L :=
    quotientAlgebraBaseChangeAlgEquiv (IsLocalRing.maximalIdeal R)
      (IsNoetherian.noetherian _) L
  exact IsRegularRing.of_ringEquiv
    (e.symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm R L
        (AdicCompletion (IsLocalRing.maximalIdeal R) R)).toRingEquiv)

end AdicCompletion
