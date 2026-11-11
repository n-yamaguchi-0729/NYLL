/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingAlgebra
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Reduction from the original quotient presentation

The coefficient map to the constructed algebra modulo the parameter kills
the parameter square and descends to the original coefficient quotient.
Polynomial evaluation then kills the original presentation kernel and
descends through its native quotient equivalence. This constructs the map
from the original algebra, retaining its generator and coefficient triangles,
without adding an algebra structure on the target coefficient quotient.
-/

@[expose] public section

noncomputable section

universe u v w t z

namespace Algebra

open MvPolynomial

/-- The actual original algebra presented over `R/(π²)` maps to the lifting
algebra modulo `π`. The map is constructed from the lifted original equations
and preserves all original coordinates and base coefficients. -/
theorem Presentation.exists_principal_lifting_reductionMap
    {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]
    (π : R) {B : Type w} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    {n : Type t} {m : Type z}
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hf : ∀ j, map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) = P.relation j)
    (θ : MvPolynomial (n ⊕ m) R →ₐ[R] D)
    (hθ : ∀ j, θ (principalLiftingRelation π f j) = 0) :
    ∃ γ : B →+* D ⧸ Ideal.span {algebraMap R D π},
      (∀ i, γ (P.val i) = Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (θ (X (Sum.inl i)))) ∧
      (∀ r : R, γ (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (algebraMap R D r)) ∧
      γ.comp ((algebraMap P.Ring B).comp
          (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})))) =
        (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})).comp
          (θ.comp (rename Sum.inl)).toRingHom := by
  let ρ : R →+* R ⧸ Ideal.span {π ^ 2} := Ideal.Quotient.mk (Ideal.span {π ^ 2})
  let τ : D →+* D ⧸ Ideal.span {algebraMap R D π} :=
    Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
  let c : R →+* D ⧸ Ideal.span {algebraMap R D π} := τ.comp (algebraMap R D)
  have hπ : τ (algebraMap R D π) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have hcsquare : c (π ^ 2) = 0 := by
    change τ (algebraMap R D (π ^ 2)) = 0
    rw [map_pow, map_pow, hπ, pow_two, mul_zero]
  have hcker : Ideal.span {π ^ 2} ≤ RingHom.ker c := by
    apply Ideal.span_le.mpr
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact hcsquare
  let ν : (R ⧸ Ideal.span {π ^ 2}) →+* D ⧸ Ideal.span {algebraMap R D π} :=
    Ideal.Quotient.lift (Ideal.span {π ^ 2}) c (fun r hr => hcker hr)
  have hν (r : R) : ν (ρ r) = τ (algebraMap R D r) := rfl
  let η : P.Ring →+* D ⧸ Ideal.span {algebraMap R D π} :=
    eval₂Hom ν (fun i => τ (θ (X (Sum.inl i))))
  let ηR : MvPolynomial n R →+* D ⧸ Ideal.span {algebraMap R D π} :=
    τ.comp (θ.comp (rename Sum.inl)).toRingHom
  have heval : η.comp (map ρ) = ηR := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change eval₂Hom ν (fun i => τ (θ (X (Sum.inl i)))) (map ρ (C r)) =
        τ (θ (rename Sum.inl (C r)))
      rw [map_C, eval₂Hom_C, hν, rename_C, algHom_C]
    · intro i
      change eval₂Hom ν (fun i => τ (θ (X (Sum.inl i)))) (map ρ (X i)) =
        τ (θ (rename Sum.inl (X i)))
      rw [map_X, eval₂Hom_X', rename_X]
  have hker : P.ker ≤ RingHom.ker η := by
    conv_lhs => rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change η (P.relation j) = 0
    rw [← hf j]
    have heq := RingHom.congr_fun heval (f j)
    change η (map ρ (f j)) = τ (θ (rename Sum.inl (f j))) at heq
    rw [heq]
    have hj := hθ j
    rw [principalLiftingRelation, map_sub, map_mul, algHom_C, sub_eq_zero] at hj
    rw [hj, map_mul, hπ, zero_mul]
  let γQ : P.Quotient →+* D ⧸ Ideal.span {algebraMap R D π} :=
    Ideal.Quotient.lift P.ker η (fun p hp => hker hp)
  let γ : B →+* D ⧸ Ideal.span {algebraMap R D π} :=
    γQ.comp P.quotientEquiv.symm.toRingHom
  have hγ (p : P.Ring) : γ (algebraMap P.Ring B p) = η p := by
    change γQ (P.quotientEquiv.symm (algebraMap P.Ring B p)) = η p
    simpa only [← P.quotientEquiv_mk p, AlgEquiv.symm_apply_apply] using
      (show γQ (Ideal.Quotient.mk P.ker p) = η p from rfl)
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro i
    have hi : algebraMap P.Ring B (X i) = P.val i := by
      rw [P.algebraMap_apply, aeval_X]
    rw [← hi, hγ]
    exact eval₂Hom_X' ν (fun i => τ (θ (X (Sum.inl i)))) i
  · intro r
    have hr : algebraMap P.Ring B (C (ρ r)) =
        algebraMap (R ⧸ Ideal.span {π ^ 2}) B (ρ r) := by
      rw [P.algebraMap_apply, aeval_C]
    rw [← hr, hγ]
    change eval₂Hom ν (fun i => τ (θ (X (Sum.inl i)))) (C (ρ r)) =
      τ (algebraMap R D r)
    rw [eval₂Hom_C, hν]
  · apply RingHom.ext
    intro p
    change γ (algebraMap P.Ring B (map ρ p)) = ηR p
    rw [hγ]
    exact RingHom.congr_fun heval p

end Algebra
