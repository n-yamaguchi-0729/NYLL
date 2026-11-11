/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.MvPolynomialCoordinateTranslation
public import Nyll.SchemeTheory.RingTheory.Smooth.GeneralCubicCorrectionSmoothFactorization
public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.MatrixMinorCubicFactorization

/-!
# Smooth factorization at an actual approximate section

Translate the original polynomial presentation by the specified approximate
section. The fourth-order maximal-minor congruence constructs the scaled
Jacobian inverse. Cubic correction and residual-ideal removal then construct
a smooth factorization of the original map, with the original quotient
retained through the actual translation equivalence.
-/

@[expose] public section

noncomputable section

universe u v w t z

open MvPolynomial
open scoped Matrix

namespace Algebra

/-- Translate the actual approximate section and construct its smooth core
with the residual quotient retained. The ideal bounds follow from the original
polynomial relations; no annihilator controller is required. -/
theorem exists_residual_quotient_factorization_at_approximate_section
    {R : Type u} {L : Type v} {m : Type w} {n : Type t} {k : Type z}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (a : n → R)
    (hminor : π ∈ Ideal.span (Set.range fun c : m → n =>
      ((Matrix.of fun j i => aeval a (pderiv i (f j))).submatrix _root_.id c).det) ⊔
        Ideal.span {π ^ 4})
    (hf : ∀ j, π ^ 4 ∣ aeval a (f j))
    (hh : ∀ j, π ^ 4 ∣ aeval a (h j))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstable : ∀ x : L,
      algebraMap R L π ^ 2 * x = 0 → algebraMap R L π * x = 0)
    (φ : (MvPolynomial n R ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L)
    (zeta : n → L)
    (hzeta : ∀ i, φ (Ideal.Quotient.mk
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i)) -
        algebraMap R L (a i) = algebraMap R L π ^ 4 * zeta i) :
    ∃ (B : Type (max u w t)) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ J : Ideal B,
        J.FG ∧ J ≤ Ideal.span {algebraMap R B π ^ 2} ∧
        Ideal.span {algebraMap R B π} * J ≤ J ^ 2 ∧
        ∃ (α : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] B ⧸ J)
          (β : B ⧸ J →ₐ[R] L), β.comp α = φ := by
  classical
  let _ : Fintype n := Fintype.ofFinite n
  let τ := coordinateTranslation a
  let f' : m → MvPolynomial n R := fun j => τ (f j)
  let h' : k → MvPolynomial n R := fun j => τ (h j)
  let I : Ideal (MvPolynomial n R) :=
    Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)
  let J : Ideal (MvPolynomial n R) :=
    Ideal.span (Set.range f') ⊔ Ideal.span (Set.range h')
  have hIJ : I.map τ.toAlgHom.toRingHom = J := by
    change Ideal.map (coordinateTranslation a).toAlgHom.toRingHom
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) = _
    rw [Ideal.map_sup, coordinateTranslation_map_span, coordinateTranslation_map_span]
  let E : (MvPolynomial n R ⧸ I) ≃ₐ[R] (MvPolynomial n R ⧸ J) :=
    Ideal.quotientEquivAlg I J τ hIJ.symm
  let φ' : (MvPolynomial n R ⧸ J) →ₐ[R] L := φ.comp E.symm.toAlgHom
  have hφ' : φ'.comp E.toAlgHom = φ := by
    apply AlgHom.ext
    intro x
    exact congrArg φ (E.symm_apply_apply x)
  have hcoordinate (i : n) : φ' (Ideal.Quotient.mk J (X i)) =
      algebraMap R L π ^ 4 * zeta i := by
    change φ (Ideal.Quotient.mk I ((coordinateTranslation a).symm (X i))) = _
    rw [coordinateTranslation_symm_X, map_sub, map_sub]
    have hC : φ (Ideal.Quotient.mk I (C (a i))) = algebraMap R L (a i) :=
      φ.commutes (a i)
    rw [hC]
    exact hzeta i
  obtain ⟨u, hu, S, hS⟩ :=
    Matrix.exists_mul_eq_smul_one_of_mem_maximalMinors_sup_pow_four
      (Matrix.of fun j i => aeval a (pderiv i (f j))) π hminor
  have hu' : π ∣ u - 1 := (dvd_pow_self π (by decide : 3 ≠ 0)).trans hu
  have hS' : Matrix.of (fun j i => constantCoeff (pderiv i (f' j))) * S =
      (u * π) • (1 : Matrix m m R) := by
    simpa only [f', τ, constantCoeff_pderiv_coordinateTranslation] using hS
  have hf' (j : m) : π ^ 4 ∣ constantCoeff (f' j) := by
    simpa only [f', τ, constantCoeff_coordinateTranslation] using hf j
  have hh' (j : k) : π ^ 4 ∣ constantCoeff (h' j) := by
    simpa only [h', τ, constantCoeff_coordinateTranslation] using hh j
  have hrelations' (j : k) : C π * h' j ∈ Ideal.span (Set.range f') ⊔
      (Ideal.span (Set.range f') ⊔ Ideal.span (Set.range h')) ^ 2 := by
    have hj := Ideal.mem_map_of_mem
      (coordinateTranslation a).toAlgHom.toRingHom (hrelations j)
    simp only [Ideal.map_sup, Ideal.map_pow, coordinateTranslation_map_span] at hj
    change coordinateTranslation a (C π * h j) ∈ _ at hj
    simpa only [map_mul, coordinateTranslation_C] using hj
  obtain ⟨B, _, _, hB, K, hKfg, hK, hrelK, α, β, hβα⟩ :=
    exists_residual_quotient_factorization_of_general_cubic_correction_data
      π u f' h' S hS' hu' hf' hh' hrelations' hπ hstable φ' zeta hcoordinate
  refine ⟨B, inferInstance, inferInstance, hB, K, hKfg, hK, hrelK,
    α.comp E.toAlgHom, β, ?_⟩
  rw [← AlgHom.comp_assoc, hβα]
  exact hφ'

/-- A fourth-order approximate section and its original Jacobian-minor
congruence construct a smooth factorization of the original quotient map.
The approximate section need not be the zero point, and no matrix inverse
or smooth algebra is supplied as an input. -/
theorem exists_smooth_factorization_at_approximate_section
    {R : Type u} {L : Type v} {m : Type w} {n : Type t} {k : Type z}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [Fintype m] [Finite n] [DecidableEq m]
    (π r : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (a : n → R)
    (hminor : π ∈ Ideal.span (Set.range fun c : m → n =>
      ((Matrix.of fun j i => aeval a (pderiv i (f j))).submatrix _root_.id c).det) ⊔
        Ideal.span {π ^ 4})
    (hf : ∀ j, π ^ 4 ∣ aeval a (f j))
    (hh : ∀ j, π ^ 4 ∣ aeval a (h j))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstable : ∀ x : L,
      algebraMap R L π ^ 2 * x = 0 → algebraMap R L π * x = 0)
    (hcontrol : ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0)
    (hr : IsUnit (algebraMap R L r))
    (φ : (MvPolynomial n R ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L)
    (zeta : n → L)
    (hzeta : ∀ i, φ (Ideal.Quotient.mk
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i)) -
        algebraMap R L (a i) = algebraMap R L π ^ 4 * zeta i) :
    ∃ (D : Type (max u w t)) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧
        ∃ (α : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] D)
          (β : D →ₐ[R] L), β.comp α = φ := by
  obtain ⟨B, _, _, hB, J, _hJfg, hJ, hrel, α, β, hβα⟩ :=
    exists_residual_quotient_factorization_at_approximate_section
      π f h a hminor hf hh hrelations hπ hstable φ zeta hzeta
  have : Smooth R B := hB
  obtain ⟨D, _, _, hD, γ, δ, hδγ⟩ :=
    exists_smooth_factorization_of_residual_quotient π r hcontrol hπ hr J hJ hrel α β
  exact ⟨D, inferInstance, inferInstance, hD, γ, δ, hδγ.trans hβα⟩

end Algebra
