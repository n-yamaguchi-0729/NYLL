/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SmoothPrimeRelationDenominators
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Strictly standard data in the original presentation

At a smooth prime, choose the original relation basis and its common
denominator. The actual split cotangent map supplies a right inverse for
the evaluated Jacobian. Expanding the determinant of this product selects
a maximal minor which is a unit in the local ring. Multiplying it by the
common denominator gives the required polynomial parameter outside the
prime, retaining all original residual relations.
-/

@[expose] public section

noncomputable section

universe u v w t

open scoped TensorProduct BigOperators

private theorem exists_isUnit_maximalMinor_of_mul_eq_one
    {T m n : Type*} [CommRing T] [IsLocalRing T] [Fintype m] [Fintype n]
    [DecidableEq m] (A : Matrix m n T) (S : Matrix n m T) (hAS : A * S = 1) :
    ∃ c : m → n, IsUnit ((A.submatrix _root_.id c).det) := by
  classical
  have hdet : (A * S).det =
      ∑ c : m → n, (A.submatrix _root_.id c).det * ∏ i, S (c i) i := by
    simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
      Finset.mul_sum, Fintype.piFinset_univ, Matrix.submatrix_apply, id_eq,
      Finset.prod_mul_distrib, mul_assoc, mul_comm]
    rw [Finset.sum_comm]
  have hunit : IsUnit (∑ c : m → n, (A.submatrix _root_.id c).det * ∏ i, S (c i) i) := by
    rw [← hdet, hAS, Matrix.det_one]
    exact isUnit_one
  obtain ⟨c, _, hc⟩ := IsLocalRing.exists_of_isUnit_sum hunit
  exact ⟨c, isUnit_of_mul_isUnit_left hc⟩

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- Actual finite strictly-standard presentation data at a smooth prime.
The parameter is a polynomial, with no assertion that it comes from the base. -/
theorem Presentation.exists_strictStandard_data_at_smoothPrime
    {ι : Type w} {σ : Type t} [Finite ι] [Finite σ] (P : Presentation R B ι σ)
    (p : Ideal B) [p.IsPrime] [IsSmoothAt R p] :
    ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ) (d : P.Ring),
      algebraMap P.Ring B d ∉ p ∧
      d ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
        ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
          _root_.id c).det)) ∧
      ∀ j, d * P.relation j ∈
        Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨κ, hκ, a, b, d₀, hb, hd₀, hres⟩ :=
    P.exists_relationBasis_and_residualParameter_at_smoothPrime p
  let _ : Fintype κ := hκ
  let T := Localization.AtPrime p
  obtain ⟨l, hl⟩ :=
    P.toGenerators.exists_retraction_baseChangeCotangent_of_formallySmooth_localization
      p.primeCompl T
  let bN : Module.Basis ι T (T ⊗[B] P.toExtension.CotangentSpace) :=
    P.cotangentSpaceBasis.baseChange T
  let D : Matrix ι κ T :=
    LinearMap.toMatrix b bN (P.toExtension.cotangentComplex.baseChange T)
  let L : Matrix κ ι T := LinearMap.toMatrix bN b l
  have hLD : L * D = 1 := by
    change LinearMap.toMatrix bN b l *
      LinearMap.toMatrix b bN (P.toExtension.cotangentComplex.baseChange T) = 1
    rw [← LinearMap.toMatrix_comp b bN b, hl, LinearMap.toMatrix_id]
  have hDL : D.transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, hLD, Matrix.transpose_one]
  obtain ⟨c, hc⟩ := exists_isUnit_maximalMinor_of_mul_eq_one D.transpose L.transpose hDL
  let A₀ : Matrix κ ι P.Ring :=
    Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))
  let ψ : P.Ring →+* T := (algebraMap B T).comp (algebraMap P.Ring B)
  have hD : D.transpose = A₀.map ψ := by
    ext j i
    dsimp only [D, bN]
    rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, hb,
      LinearMap.baseChange_tmul, Extension.cotangentComplex_mk,
      Module.Basis.baseChange_repr_tmul,
      Generators.cotangentSpaceBasis_repr_one_tmul]
    change MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation (a j))) •
        (1 : T) = algebraMap B T
        (algebraMap P.Ring B (MvPolynomial.pderiv i (P.relation (a j))))
    rw [Algebra.smul_def, mul_one, P.algebraMap_apply]
  let δ : P.Ring := (A₀.submatrix _root_.id c).det
  have hδunit : IsUnit (ψ δ) := by
    dsimp only [δ]
    rw [RingHom.map_det]
    change IsUnit (((A₀.map ψ).submatrix _root_.id c).det)
    rw [← hD]
    exact hc
  have hδ : algebraMap P.Ring B δ ∉ p := by
    change IsUnit (algebraMap B T (algebraMap P.Ring B δ)) at hδunit
    exact (IsLocalization.AtPrime.isUnit_to_map_iff T p _).mp hδunit
  refine ⟨κ, hκ, Classical.decEq κ, a, d₀ * δ, ?_, ?_, fun j => ?_⟩
  · rw [map_mul]
    exact p.primeCompl.mul_mem hd₀ hδ
  · apply (show Ideal.span (Set.range (fun c : κ → ι =>
        (A₀.submatrix _root_.id c).det)) ≤ P.ker ⊔
        Ideal.span (Set.range (fun c : κ → ι => (A₀.submatrix _root_.id c).det))
      from le_sup_right)
    exact (Ideal.span (Set.range (fun c : κ → ι =>
      (A₀.submatrix _root_.id c).det))).mul_mem_left d₀ (Ideal.subset_span (Set.mem_range_self c))
  · have hj := (Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2).mul_mem_left
      δ (hres j)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hj

end Algebra
