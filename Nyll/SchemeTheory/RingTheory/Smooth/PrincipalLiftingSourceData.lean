/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Actual source data for principal lifting

Lift the original quotient-presentation relations through the coefficient
quotient and lift the images of its original generators through the target
quotient. The supplied coefficient triangle proves a polynomial evaluation
triangle on all polynomials. The original relations therefore evaluate to
actual multiples of the squared parameter in the target.

Only the existing algebra structures on the source presentation and target
are used. The original quotient map is a ring homomorphism; no additional
algebra structure on either quotient is introduced.
-/

@[expose] public section

noncomputable section

universe u v w t z

namespace Algebra

open MvPolynomial

/-- A genuine map from the original quotient presentation to the target
modulo the parameter square produces polynomial relation lifts, actual
coordinate representatives, and exact squared-parameter errors. The full
polynomial evaluation triangle retains the original map. -/
theorem Presentation.exists_principal_lifting_source_data
    {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    (π : R) {B : Type w} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    {n : Type t} {m : Type z}
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (α : B →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2})
    (hα : ∀ r : R,
      α (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2}) (algebraMap R L r)) :
    ∃ (f : m → MvPolynomial n R) (xval : n → L) (μ : m → L),
      (∀ j, map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) = P.relation j) ∧
      (∀ i, Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2}) (xval i) =
        α (P.val i)) ∧
      (∀ j, aeval xval (f j) = (algebraMap R L π) ^ 2 * μ j) ∧
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})).comp
          (aeval xval).toRingHom =
        α.comp ((algebraMap P.Ring B).comp
          (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})))) := by
  classical
  let ρ : R →+* R ⧸ Ideal.span {π ^ 2} := Ideal.Quotient.mk (Ideal.span {π ^ 2})
  let τ : L →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2} :=
    Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})
  have hrelations (j : m) : ∃ p : MvPolynomial n R, map ρ p = P.relation j :=
    map_surjective ρ Ideal.Quotient.mk_surjective (P.relation j)
  choose f hf using hrelations
  have hcoordinates (i : n) : ∃ x : L, τ x = α (P.val i) :=
    Ideal.Quotient.mk_surjective (α (P.val i))
  choose xval hxval using hcoordinates
  have heval : τ.comp (aeval xval).toRingHom =
      α.comp ((algebraMap P.Ring B).comp (map ρ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change τ (aeval xval (C r)) = α (algebraMap P.Ring B (map ρ (C r)))
      rw [aeval_C, map_C, P.algebraMap_apply, aeval_C]
      exact (hα r).symm
    · intro i
      change τ (aeval xval (X i)) = α (algebraMap P.Ring B (map ρ (X i)))
      rw [aeval_X, map_X, P.algebraMap_apply, aeval_X]
      exact hxval i
  have herrors (j : m) : ∃ μ : L, aeval xval (f j) =
      (algebraMap R L π) ^ 2 * μ := by
    have hzero : τ (aeval xval (f j)) = 0 := by
      have heq := RingHom.congr_fun heval (f j)
      change τ (aeval xval (f j)) = α (algebraMap P.Ring B (map ρ (f j))) at heq
      rw [hf j] at heq
      have hrel : algebraMap P.Ring B (P.relation j) = 0 := P.relation_mem_ker j
      rw [hrel, map_zero] at heq
      exact heq
    have hmem : aeval xval (f j) ∈ Ideal.span {(algebraMap R L π) ^ 2} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hzero
    exact Ideal.mem_span_singleton.mp hmem
  choose μ hμ using herrors
  exact ⟨f, xval, μ, hf, hxval, hμ, heval⟩

end Algebra
