/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientPresheaf
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Change of coefficients for the literal scalar quotient

An equivalence of tensor algebras over the test algebra preserves the actual
scalar-unit subgroup. In particular, tensor-product cancellation gives the
coefficient base-change comparison over every test algebra. This is the
algebraic comparison; its compatibility with the represented group schemes
is a separate construction.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace SchemeTheory.Affine.ScalarQuotientPresheaf

section GeneralScalarUnits

variable {S B C : Type u} [CommRing S] [CommRing B] [CommRing C]
  [Algebra S B] [Algebra S C]

/-- An algebra equivalence preserves precisely the image of scalar units. -/
theorem map_scalarUnitRange (e : B ≃ₐ[S] C) :
    (Units.map (algebraMap S B).toMonoidHom).range.map
        (Units.mapEquiv e.toMulEquiv).toMonoidHom =
      (Units.map (algebraMap S C).toMonoidHom).range := by
  have hs (a : Sˣ) :
      Units.mapEquiv e.toMulEquiv (Units.map (algebraMap S B).toMonoidHom a) =
        Units.map (algebraMap S C).toMonoidHom a := Units.ext (e.commutes (a : S))
  ext a
  constructor
  · rintro ⟨x, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, (hs r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨Units.map (algebraMap S B).toMonoidHom r, ⟨r, rfl⟩, hs r⟩

/-- The scalar-unit quotient comparison for arbitrary actual algebras. -/
def scalarUnitQuotientEquiv (e : B ≃ₐ[S] C) :
    Bˣ ⧸ (Units.map (algebraMap S B).toMonoidHom).range ≃*
      Cˣ ⧸ (Units.map (algebraMap S C).toMonoidHom).range :=
  QuotientGroup.congr _ _ (Units.mapEquiv e.toMulEquiv) (map_scalarUnitRange e)

theorem scalarUnitQuotientEquiv_mk (e : B ≃ₐ[S] C) (a : Bˣ) :
    scalarUnitQuotientEquiv e (QuotientGroup.mk a) =
      QuotientGroup.mk (Units.mapEquiv e.toMulEquiv a) := rfl

end GeneralScalarUnits

section Equivalence

variable {R R' A A' S : Type u}
  [CommRing R] [CommRing R'] [CommRing A] [CommRing A'] [CommRing S]
  [Algebra R A] [Algebra R S] [Algebra R' A'] [Algebra R' S]

/-- Test-algebra-linear equivalences preserve the scalar units exactly. -/
theorem tensorEquiv_scalarHom (e : (S ⊗[R] A) ≃ₐ[S] (S ⊗[R'] A')) (r : Sˣ) :
    Units.mapEquiv e.toMulEquiv (scalarHom (R := R) (A := A) r) =
      scalarHom (R := R') (A := A') r := by
  apply Units.ext
  exact e.commutes (r : S)

/-- The subgroup relation used in the quotient is carried to the actual
scalar subgroup, rather than assumed to be compatible with the equivalence. -/
theorem map_scalarSubgroup (e : (S ⊗[R] A) ≃ₐ[S] (S ⊗[R'] A')) :
    (scalarSubgroup (R := R) (A := A) (S := S)).map
        (Units.mapEquiv e.toMulEquiv).toMonoidHom =
      scalarSubgroup (R := R') (A := A') (S := S) := by
  ext a
  constructor
  · rintro ⟨x, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, (tensorEquiv_scalarHom e r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨scalarHom (R := R) (A := A) r, ⟨r, rfl⟩, tensorEquiv_scalarHom e r⟩

/-- The actual scalar quotient transported through an equivalence of
tensor algebras over the test algebra. -/
def quotientEquivOfTensorEquiv (e : (S ⊗[R] A) ≃ₐ[S] (S ⊗[R'] A')) :
    ScalarQuotient (R := R) (A := A) (S := S) ≃*
      ScalarQuotient (R := R') (A := A') (S := S) :=
  QuotientGroup.congr _ _ (Units.mapEquiv e.toMulEquiv) (map_scalarSubgroup e)

theorem quotientEquivOfTensorEquiv_mk
    (e : (S ⊗[R] A) ≃ₐ[S] (S ⊗[R'] A')) (a : (S ⊗[R] A)ˣ) :
    quotientEquivOfTensorEquiv e (QuotientGroup.mk a) =
      QuotientGroup.mk (Units.mapEquiv e.toMulEquiv a) := rfl

end Equivalence

variable {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Base-changing the coefficient algebra and then evaluating on a test
algebra gives the same quotient of units by its scalar units. -/
def coefficientBaseChangeEquiv :
    ScalarQuotient (R := S) (A := S ⊗[R] A) (S := T) ≃*
      ScalarQuotient (R := R) (A := A) (S := T) :=
  quotientEquivOfTensorEquiv (Algebra.TensorProduct.cancelBaseChange R S T T A)

/-- On actual unit representatives the comparison is the canonical tensor
base-change cancellation, including for nonreduced coefficient algebras. -/
theorem coefficientBaseChangeEquiv_mk (a : (T ⊗[S] (S ⊗[R] A))ˣ) :
    coefficientBaseChangeEquiv (R := R) (S := S) (T := T) (A := A)
        (QuotientGroup.mk a) =
      QuotientGroup.mk (Units.mapEquiv
        (Algebra.TensorProduct.cancelBaseChange R S T T A).toMulEquiv a) := rfl

variable {T' : Type u} [CommRing T'] [Algebra R T'] [Algebra S T']
  [IsScalarTower R S T']

private theorem cancelBaseChange_map (g : T →ₐ[S] T') (x : T ⊗[S] (S ⊗[R] A)) :
    Algebra.TensorProduct.cancelBaseChange R S T' T' A
        (Algebra.TensorProduct.map g (AlgHom.id S (S ⊗[R] A)) x) =
      Algebra.TensorProduct.map (g.restrictScalars R) (AlgHom.id R A)
        (Algebra.TensorProduct.cancelBaseChange R S T T A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul s a =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.cancelBaseChange_tmul, AlgHom.restrictScalars_apply, map_smul]

/-- The coefficient comparison is natural in every homomorphism of test
algebras. Thus it compares the quotient functors, not only their point sets. -/
theorem coefficientBaseChangeEquiv_quotientMap (g : T →ₐ[S] T')
    (q : ScalarQuotient (R := S) (A := S ⊗[R] A) (S := T)) :
    coefficientBaseChangeEquiv (R := R) (S := S) (T := T') (A := A)
        (quotientMap g q) =
      quotientMap (g.restrictScalars R)
        (coefficientBaseChangeEquiv (R := R) (S := S) (T := T) (A := A) q) := by
  refine QuotientGroup.induction_on q fun a => ?_
  change QuotientGroup.mk
      (Units.mapEquiv (Algebra.TensorProduct.cancelBaseChange R S T' T' A).toMulEquiv
        (unitMap g a)) =
    QuotientGroup.mk (unitMap (g.restrictScalars R)
      (Units.mapEquiv (Algebra.TensorProduct.cancelBaseChange R S T T A).toMulEquiv a))
  apply congrArg QuotientGroup.mk
  apply Units.ext
  exact cancelBaseChange_map g (a : T ⊗[S] (S ⊗[R] A))

end SchemeTheory.Affine.ScalarQuotientPresheaf
