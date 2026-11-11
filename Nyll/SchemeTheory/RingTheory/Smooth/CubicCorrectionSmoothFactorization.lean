/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PolynomialCubicCorrection
public import Nyll.SchemeTheory.RingTheory.Smooth.TriangularCorrectionSmooth
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# An actual smooth factorization from cubic correction equations

For a finite presentation with a scaled right inverse to its constant
Jacobian, a fourth-order approximate section produces an actual smooth
factorization of the original map to a local target. Annihilator stability
handles the zero-divisor case; no cancellation by the parameter is assumed.

This proves the complete-intersection calculation in Stacks 07CR. Producing
such presentation data for an arbitrary map to a completion, and the
desingularization induction for general presentations, remain separate tasks.
-/

@[expose] public section

noncomputable section

universe u v w t

open MvPolynomial
open scoped Matrix

namespace Algebra

private theorem eq_zero_of_dvd_of_cube_mul_eq_zero
    {L : Type*} [CommRing L] (a x : L)
    (hstable : ∀ z : L, a ^ 2 * z = 0 → a * z = 0)
    (hdiv : a ∣ x) (hzero : a ^ 3 * x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := hdiv
  have hfour : a ^ 2 * (a ^ 2 * z) = 0 := by
    calc
      a ^ 2 * (a ^ 2 * z) = a ^ 3 * (a * z) := by ring
      _ = 0 := hzero
  have hthree : a ^ 2 * (a * z) = 0 := by
    calc
      a ^ 2 * (a * z) = a * (a ^ 2 * z) := by ring
      _ = 0 := hstable _ hfour
  have htwo : a ^ 2 * z = 0 := by
    calc
      a ^ 2 * z = a * (a * z) := by ring
      _ = 0 := hstable _ hthree
  exact hstable _ htwo

/-- Explicit fourth-order approximate-section data and a scaled Jacobian
inverse produce a smooth factorization of the original presented-algebra
map. The target need not be a domain, and smoothness is constructed. -/
theorem exists_smooth_factorization_of_cubic_correction_data_with_coordinates
    {R : Type u} {L : Type v} {m : Type w} {n : Type t}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [Finite m] [Fintype n] [DecidableEq m]
    (π u : R) (f : m → MvPolynomial n R) (S : Matrix n m R)
    (hS : Matrix.of (fun j i => constantCoeff (pderiv i (f j))) * S =
      (u * π) • (1 : Matrix m m R))
    (hu : π ∣ u - 1) (hf : ∀ j, π ^ 4 ∣ constantCoeff (f j))
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstable : ∀ z : L,
      algebraMap R L π ^ 2 * z = 0 → algebraMap R L π * z = 0)
    (φ : (MvPolynomial n R ⧸ Ideal.span (Set.range f)) →ₐ[R] L)
    (zeta : n → L)
    (hzeta : ∀ i, φ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i)) =
      algebraMap R L π ^ 4 * zeta i) :
    ∃ (D : Type (max u w t)) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧
        ∃ (α : (MvPolynomial n R ⧸ Ideal.span (Set.range f)) →ₐ[R] D)
          (β : D →ₐ[R] L), β.comp α = φ ∧
            ∀ i, α (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i)) ∈
              Ideal.span {algebraMap R D π ^ 2} := by
  classical
  let _ : Fintype m := Fintype.ofFinite m
  obtain ⟨g, hg⟩ := exists_polynomial_cubic_corrections π u f S hS hu hf
  let P := MvPolynomial (m ⊕ n) R
  let a : L := algebraMap R L π
  let e : P →ₐ[R] L := aeval (Sum.elim (fun _ : m => 0) (fun i : n => a * zeta i))
  have heC (r : R) : e (C r) = algebraMap R L r := aeval_C _ r
  have heX₁ (j : m) : e (X (Sum.inl j)) = 0 := aeval_X _ _
  have heX₂ (i : n) : e (X (Sum.inr i)) = a * zeta i := aeval_X _ _
  let qf : MvPolynomial n R →ₐ[R]
      (MvPolynomial n R ⧸ Ideal.span (Set.range f)) :=
    Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))
  have hsubX (i : n) : e (cubicCorrectionSubstitution π S i) = a ^ 4 * zeta i := by
    change aeval (Sum.elim (fun _ : m => 0) (fun i : n => a * zeta i))
      (C π ^ 2 * ((S.map C) *ᵥ fun j => X (Sum.inl j)) i +
        C π ^ 3 * X (Sum.inr i)) = a ^ 4 * zeta i
    simp only [map_add, map_mul, map_pow, aeval_C, Matrix.mulVec, dotProduct,
      Matrix.map_apply, map_sum, aeval_X, Sum.elim_inl, Sum.elim_inr,
      mul_zero, Finset.sum_const_zero, zero_add]
    change a ^ 3 * (a * zeta i) = a ^ 4 * zeta i
    ring
  have hsub : e.comp (aeval (cubicCorrectionSubstitution π S)) = φ.comp qf := by
    apply MvPolynomial.algHom_ext
    intro i
    change e (aeval (cubicCorrectionSubstitution π S) (X i)) =
      φ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i))
    rw [aeval_X, hsubX, hzeta]
  have hcube (j : m) : a ^ 3 * e (g j) = 0 := by
    have h := congrArg e (hg j).1
    have hz : e (aeval (cubicCorrectionSubstitution π S) (f j)) = 0 := by
      change (e.comp (aeval (cubicCorrectionSubstitution π S))) (f j) = 0
      rw [hsub]
      change φ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (f j)) = 0
      rw [Ideal.Quotient.mk_span_range, map_zero]
    rw [hz, map_mul, map_pow, heC] at h
    exact h.symm
  have hdiv (j : m) : a ∣ e (g j) := by
    obtain ⟨q, hq⟩ := (hg j).2
    have h := congrArg e hq
    simp only [map_sub, map_add, map_sum, map_mul, heC, heX₁, heX₂] at h
    change e (g j) -
      (0 + ∑ i, algebraMap R L (constantCoeff (pderiv i (f j))) * (a * zeta i)) =
      a * e q at h
    rw [zero_add] at h
    refine ⟨e q + ∑ i, algebraMap R L (constantCoeff (pderiv i (f j))) * zeta i, ?_⟩
    calc
      e (g j) =
          (e (g j) - ∑ i, algebraMap R L (constantCoeff (pderiv i (f j))) *
            (a * zeta i)) +
          ∑ i, algebraMap R L (constantCoeff (pderiv i (f j))) * (a * zeta i) := by ring
      _ = a * e q +
          ∑ i, algebraMap R L (constantCoeff (pderiv i (f j))) * (a * zeta i) := by rw [h]
      _ = a * (e q + ∑ i,
          algebraMap R L (constantCoeff (pderiv i (f j))) * zeta i) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have hgzero (j : m) : e (g j) = 0 :=
    eq_zero_of_dvd_of_cube_mul_eq_zero a (e (g j)) hstable (hdiv j) (hcube j)
  let Q := P ⧸ Ideal.span (Set.range g)
  let qg : P →ₐ[R] Q := Ideal.Quotient.mkₐ R (Ideal.span (Set.range g))
  have hker : Ideal.span (Set.range g) ≤ RingHom.ker e.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hgzero j
  let β₀ : Q →ₐ[R] L :=
    Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) e (fun p hp => hker hp)
  have hβ₀ : β₀.comp qg = e :=
    Ideal.Quotient.liftₐ_comp _ _ _
  obtain ⟨d, hD, β, hβ⟩ := exists_standardSmooth_localization_of_triangular_relations
    π (fun j i => constantCoeff (pderiv i (f j))) g (fun j => (hg j).2) β₀ hπ
  have : IsStandardSmooth R (Localization.Away d) := hD
  let ℓ : Q →ₐ[R] Localization.Away d := IsScalarTower.toAlgHom R Q (Localization.Away d)
  let α₀ : MvPolynomial n R →ₐ[R] Localization.Away d :=
    ℓ.comp (qg.comp (aeval (cubicCorrectionSubstitution π S)))
  have hαzero (j : m) : α₀ (f j) = 0 := by
    change ℓ (qg (aeval (cubicCorrectionSubstitution π S) (f j))) = 0
    rw [(hg j).1, map_mul]
    have hqg : qg (g j) = 0 := Ideal.Quotient.mk_span_range g j
    rw [hqg, mul_zero, map_zero]
  have hkerf : Ideal.span (Set.range f) ≤ RingHom.ker α₀.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hαzero j
  let α : (MvPolynomial n R ⧸ Ideal.span (Set.range f)) →ₐ[R] Localization.Away d :=
    Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) α₀ (fun p hp => hkerf hp)
  have hα : α.comp qf = α₀ := Ideal.Quotient.liftₐ_comp _ _ _
  refine ⟨Localization.Away d, inferInstance, inferInstance, inferInstance, α, β, ?_, ?_⟩
  · apply Ideal.Quotient.algHom_ext
    change (β.comp α).comp qf = φ.comp qf
    rw [AlgHom.comp_assoc, hα]
    change β.comp (ℓ.comp (qg.comp (aeval (cubicCorrectionSubstitution π S)))) = φ.comp qf
    rw [← AlgHom.comp_assoc, hβ, ← AlgHom.comp_assoc, hβ₀]
    exact hsub
  · intro i
    let θ : P →ₐ[R] Localization.Away d := ℓ.comp qg
    let z : P := ((S.map C) *ᵥ fun j => X (Sum.inl j)) i + C π * X (Sum.inr i)
    have hδ : cubicCorrectionSubstitution π S i = C π ^ 2 * z := by
      dsimp only [cubicCorrectionSubstitution, z]
      ring
    have hθ : θ (C π) = algebraMap R (Localization.Away d) π := θ.commutes π
    apply Ideal.mem_span_singleton.mpr
    refine ⟨θ z, ?_⟩
    change θ (aeval (cubicCorrectionSubstitution π S) (X i)) =
      algebraMap R (Localization.Away d) π ^ 2 * θ z
    rw [aeval_X, hδ, map_mul, map_pow, hθ]

/-- Explicit cubic correction data produce a smooth factorization of the
original map. The strengthened producer also retains coordinate divisibility. -/
theorem exists_smooth_factorization_of_cubic_correction_data
    {R : Type u} {L : Type v} {m : Type w} {n : Type t}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [Finite m] [Fintype n] [DecidableEq m]
    (π u : R) (f : m → MvPolynomial n R) (S : Matrix n m R)
    (hS : Matrix.of (fun j i => constantCoeff (pderiv i (f j))) * S =
      (u * π) • (1 : Matrix m m R))
    (hu : π ∣ u - 1) (hf : ∀ j, π ^ 4 ∣ constantCoeff (f j))
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstable : ∀ z : L,
      algebraMap R L π ^ 2 * z = 0 → algebraMap R L π * z = 0)
    (φ : (MvPolynomial n R ⧸ Ideal.span (Set.range f)) →ₐ[R] L)
    (zeta : n → L)
    (hzeta : ∀ i, φ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i)) =
      algebraMap R L π ^ 4 * zeta i) :
    ∃ (D : Type (max u w t)) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧
        ∃ (α : (MvPolynomial n R ⧸ Ideal.span (Set.range f)) →ₐ[R] D)
          (β : D →ₐ[R] L), β.comp α = φ := by
  obtain ⟨D, _, _, hD, α, β, hcomp, _hcoordinates⟩ :=
    exists_smooth_factorization_of_cubic_correction_data_with_coordinates
      π u f S hS hu hf hπ hstable φ zeta hzeta
  exact ⟨D, inferInstance, inferInstance, hD, α, β, hcomp⟩

end Algebra
