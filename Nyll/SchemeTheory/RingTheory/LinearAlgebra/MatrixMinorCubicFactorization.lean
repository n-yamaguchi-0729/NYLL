/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.MatrixMinorScalarFactorization
public import Mathlib.RingTheory.Ideal.Span

/-!
# A scaled Jacobian inverse from the fourth-order minor congruence

Evaluating the strictly-standard minor condition at an approximate section
only gives membership modulo the fourth power of the parameter. The error
is absorbed into an actual scalar congruent to one modulo its cube. The
existing adjugate construction then supplies the actual scaled inverse.
-/

@[expose] public section

noncomputable section

namespace Matrix

/-- A maximal-minor condition modulo the fourth power supplies the
actual matrix and scalar used by cubic desingularization. -/
theorem exists_mul_eq_smul_one_of_mem_maximalMinors_sup_pow_four
    {R m n : Type*} [CommRing R] [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n R) (π : R)
    (hπ : π ∈ Ideal.span (Set.range fun c : m → n => (A.submatrix id c).det) ⊔
      Ideal.span {π ^ 4}) :
    ∃ u : R, π ^ 3 ∣ u - 1 ∧
      ∃ S : Matrix n m R, A * S = (u * π) • (1 : Matrix m m R) := by
  obtain ⟨d, hd, e, he, hde⟩ := Submodule.mem_sup.mp hπ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp he
  let u : R := 1 - π ^ 3 * c
  have hd' : d = u * π := by
    calc
      d = (d + π ^ 4 * c) - π ^ 4 * c := by ring
      _ = π - π ^ 4 * c := by rw [← hc, hde]
      _ = u * π := by dsimp only [u]; ring
  obtain ⟨S, hS⟩ := exists_mul_eq_smul_one_of_mem_span_maximalMinors A d hd
  refine ⟨u, ⟨-c, ?_⟩, S, ?_⟩
  · dsimp only [u]
    ring
  · rw [← hd']
    exact hS

end Matrix
