/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.MvPolynomialCubicCorrection
public import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Polynomial correction equations for desingularization

The scaled-Jacobian calculation is carried out in the actual polynomial
algebra on the correction variables. Its output consists of polynomial
equations, with both the original substitution identity and the triangular
reduction retained. This is the equation-producing step of Stacks 07CR.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace MvPolynomial

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]

/-- The polynomial substitution used in the cubic correction construction. -/
def cubicCorrectionSubstitution (π : R) (S : Matrix n m R) :
    n → MvPolynomial (m ⊕ n) R :=
  fun i => C π ^ 2 * ((S.map C) *ᵥ fun j => X (Sum.inl j)) i +
    C π ^ 3 * X (Sum.inr i)

/-- The correction equations exist as actual polynomials, not just as
elements chosen separately after evaluation in a target ring. -/
theorem exists_polynomial_cubic_corrections [DecidableEq m]
    (π u : R) (f : m → MvPolynomial n R) (S : Matrix n m R)
    (hS : Matrix.of (fun j i => constantCoeff (pderiv i (f j))) * S =
      (u * π) • (1 : Matrix m m R))
    (hu : π ∣ u - 1) (hf : ∀ j, π ^ 4 ∣ constantCoeff (f j)) :
    ∃ g : m → MvPolynomial (m ⊕ n) R, ∀ j,
      aeval (cubicCorrectionSubstitution π S) (f j) = C π ^ 3 * g j ∧
        C π ∣ g j - (X (Sum.inl j) +
          ∑ i, C (constantCoeff (pderiv i (f j))) * X (Sum.inr i)) := by
  classical
  let P := MvPolynomial (m ⊕ n) R
  let F : m → MvPolynomial n P := fun j => map C (f j)
  have hSP :
      Matrix.of (fun j i => constantCoeff (pderiv i (F j))) * S.map C =
        ((C u : P) * C π) • (1 : Matrix m m P) := by
    apply Matrix.ext
    intro j k
    have h := congrArg (C : R →+* P) (congrFun (congrFun hS j) k)
    simpa only [F, pderiv_map, constantCoeff_map, Matrix.mul_apply,
      Matrix.of_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, map_sum, map_mul, apply_ite, map_one, map_zero] using h
  have huP : (C π : P) ∣ C u - 1 := by
    obtain ⟨a, ha⟩ := hu
    refine ⟨C a, ?_⟩
    rw [← map_one C, ← map_sub, ha, map_mul]
  have hfP (j : m) : (C π : P) ^ 4 ∣ constantCoeff (F j) := by
    obtain ⟨a, ha⟩ := hf j
    refine ⟨C a, ?_⟩
    rw [show constantCoeff (F j) = C (constantCoeff (f j)) from
      constantCoeff_map C (f j), ha, map_mul, map_pow]
  obtain ⟨g, hg⟩ := exists_cubic_corrections_of_scaled_jacobian
    (C π : P) (C u) F (S.map C) hSP huP hfP
    (fun j => X (Sum.inl j)) (fun i => X (Sum.inr i))
  refine ⟨g, fun j => ⟨?_, ?_⟩⟩
  · have h := (hg j).1
    change aeval (cubicCorrectionSubstitution π S) (map (algebraMap R P) (f j)) =
      C π ^ 3 * g j at h
    rw [aeval_map_algebraMap] at h
    exact h
  · simpa only [F, pderiv_map, constantCoeff_map] using (hg j).2

end MvPolynomial
