/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial corrections for a finite family in an extended ideal

A finite family of elements of an extended ideal can be lifted
simultaneously to that ideal in a polynomial algebra with finitely many
variables. The polynomial evaluation map retains the original values.
The coefficients are taken from the original ideal by the finite linear
combination description of ideal extension.

These corrections are used when lifting a finite algebra presentation
from a quotient of the coefficient ring.
-/

@[expose] public section

noncomputable section

universe u v t

namespace Ideal

/-- A finite family in `I A` is the evaluation of a family in `I R[X]`,
for one polynomial algebra with finitely many variables. -/
theorem exists_finite_polynomial_corrections
    {R : Type u} {A : Type v} {ι : Type t}
    [CommRing R] [CommRing A] [Algebra R A] [Finite ι]
    (I : Ideal R) (x : ι → A)
    (hx : ∀ i, x i ∈ I.map (algebraMap R A)) :
    ∃ (σ : Type (max u t)) (_ : Fintype σ) (y : σ → A)
      (p : ι → MvPolynomial σ R),
      ∀ i, p i ∈ I.map (algebraMap R (MvPolynomial σ R)) ∧
        MvPolynomial.aeval y (p i) = x i := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hset : (algebraMap R A) '' (I : Set R) =
      Set.range (fun r : I => algebraMap R A r) := by
    ext a
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, r.property, rfl⟩
  have hc : ∀ i, ∃ c : I →₀ A,
      (c.sum fun r a => a • algebraMap R A r) = x i := by
    intro i
    apply Finsupp.mem_span_range_iff_exists_finsupp.mp
    have hi := hx i
    change x i ∈ Submodule.span A ((algebraMap R A) '' (I : Set R)) at hi
    rw [hset] at hi
    exact hi
  choose c hc using hc
  let σ := Σ i : ι, ↑(c i).support
  let y : σ → A := fun j => c j.1 j.2.1
  let p : ι → MvPolynomial σ R := fun i =>
    ∑ j : ↑(c i).support,
      MvPolynomial.C (j.1 : R) * MvPolynomial.X (⟨i, j⟩ : σ)
  refine ⟨σ, inferInstance, y, p, fun i => ⟨?_, ?_⟩⟩
  · apply Submodule.sum_mem
    intro j _hj
    apply Ideal.mul_mem_right
    exact Ideal.mem_map_of_mem (algebraMap R (MvPolynomial σ R)) j.1.property
  · change MvPolynomial.aeval y
        (∑ j : ↑(c i).support,
          MvPolynomial.C (j.1 : R) * MvPolynomial.X (⟨i, j⟩ : σ)) = x i
    rw [map_sum]
    simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    change (∑ j : ↑(c i).support,
      algebraMap R A (j.1 : R) * c i j.1) = x i
    rw [Finset.sum_coe_sort ((c i).support)
      (fun r : I => algebraMap R A r * c i r)]
    simpa only [Finsupp.sum, smul_eq_mul, mul_comm] using hc i

end Ideal
