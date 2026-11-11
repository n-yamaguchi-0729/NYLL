/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.MvPolynomialTaylorIdeal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span

/-!
# Cubic correction equations from a scaled Jacobian inverse

The substitution built from a scaled right inverse of the Jacobian
has cubic-divisible values. Dividing these values by the cube gives
actual correction equations whose reductions are the required linear
equations. No cancellation by the base element is used.

This is the polynomial correction construction in Stacks Project,
Lemma 16.7.1:
https://stacks.math.columbia.edu/tag/07CR
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace MvPolynomial

/-- A scaled Jacobian inverse and fourth-order constant terms produce
cubic correction equations with the prescribed linear reductions. -/
theorem exists_cubic_corrections_of_scaled_jacobian
    {R m n : Type*} [CommRing R] [Fintype m] [Fintype n] [DecidableEq m]
    (π u : R) (f : m → MvPolynomial n R) (S : Matrix n m R)
    (hS : Matrix.of (fun j i => constantCoeff (pderiv i (f j))) * S =
      (u * π) • (1 : Matrix m m R))
    (hu : π ∣ u - 1) (hf : ∀ j, π ^ 4 ∣ constantCoeff (f j))
    (v : m → R) (w : n → R) :
    ∃ g : m → R, ∀ j,
      aeval (fun i => π ^ 2 * (S *ᵥ v) i + π ^ 3 * w i) (f j) = π ^ 3 * g j ∧
        π ∣ g j - (v j + ∑ i, constantCoeff (pderiv i (f j)) * w i) := by
  classical
  let r : Matrix m n R := Matrix.of (fun j i => constantCoeff (pderiv i (f j)))
  let d : n → R := fun i => π ^ 2 * (S *ᵥ v) i + π ^ 3 * w i
  have hS' : r * S = (u * π) • (1 : Matrix m m R) := hS
  have hd : d = π ^ 2 • (S *ᵥ v) + π ^ 3 • w := rfl
  have hlin (j : m) :
      (r *ᵥ d) j = π ^ 3 * (u * v j + (r *ᵥ w) j) := by
    rw [hd, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hS', Matrix.smul_mulVec, Matrix.one_mulVec]
    change π ^ 2 * ((u * π) * v j) + π ^ 3 * (r *ᵥ w) j =
      π ^ 3 * (u * v j + (r *ᵥ w) j)
    ring
  let J : Ideal R := Ideal.span {π ^ 2}
  have hdJ (i : n) : d i ∈ J := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(S *ᵥ v) i + π * w i, ?_⟩
    change π ^ 2 * (S *ᵥ v) i + π ^ 3 * w i =
      π ^ 2 * ((S *ᵥ v) i + π * w i)
    ring
  have hJ : J ^ 2 = Ideal.span {π ^ 4} := by
    change Ideal.span {π ^ 2} ^ 2 = Ideal.span {π ^ 4}
    rw [Ideal.span_singleton_pow, ← pow_mul]
  have hrem (j : m) :
      π ^ 4 ∣ aeval d (f j) - constantCoeff (f j) - (r *ᵥ d) j := by
    have h := aeval_add_sub_linear_mem_ideal_sq J (0 : n → R) d hdJ (f j)
    simp only [Pi.zero_apply, zero_add, aeval_zero, Algebra.algebraMap_self_apply] at h
    rw [hJ] at h
    exact Ideal.mem_span_singleton.mp h
  obtain ⟨a, ha⟩ := hu
  have hu' : u = 1 + π * a := by
    calc
      u = (u - 1) + 1 := by ring
      _ = 1 + π * a := by rw [ha]; ring
  choose c hc using hf
  choose b hb using hrem
  let g : m → R := fun j =>
    v j + (r *ᵥ w) j + π * (b j + c j + a * v j)
  refine ⟨g, fun j => ⟨?_, ?_⟩⟩
  · have hval : aeval d (f j) =
        π ^ 4 * b j + constantCoeff (f j) + (r *ᵥ d) j := by
      calc
        aeval d (f j) =
            (aeval d (f j) - constantCoeff (f j) - (r *ᵥ d) j) +
              constantCoeff (f j) + (r *ᵥ d) j := by ring
        _ = π ^ 4 * b j + constantCoeff (f j) + (r *ᵥ d) j := by rw [hb]
    change aeval d (f j) =
      π ^ 3 * (v j + (r *ᵥ w) j + π * (b j + c j + a * v j))
    rw [hval, hc, hlin, hu']
    ring
  · refine ⟨b j + c j + a * v j, ?_⟩
    change v j + (r *ᵥ w) j + π * (b j + c j + a * v j) -
      (v j + (r *ᵥ w) j) = π * (b j + c j + a * v j)
    ring

end MvPolynomial
