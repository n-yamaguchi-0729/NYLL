/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Cyclic.LangNormKernel
import Mathlib.Tactic.Abel

/-!
# Fixed representatives of cyclic quotient classes

An equivariant quotient class fixed by a cyclic action has a fixed representative
when norm-one elements have Hilbert 90 primitives and invariant kernel elements
are norms of kernel elements. The proof explicitly removes the norm obstruction.
-/

noncomputable section

namespace CyclicAction

variable {G M D : Type*} [Group G] [AddCommGroup M] [AddCommGroup D]
    [DistribMulAction G M] [DistribMulAction G D]

/-- Remove the cyclic norm obstruction and produce an actual fixed representative. -/
theorem exists_fixed_representative (σ : G) (n : ℕ) (f : M →+ D)
    (hf : ∀ x : M, f (σ • x) = σ • f x)
    (hM : ∀ x : M, σ ^ n • x = x) (hD : ∀ x : D, σ ^ n • x = x)
    (h90 : ∀ x : M, (∑ i ∈ Finset.range n, σ ^ i • x) = 0 →
      ∃ y : M, σ • y - y = x)
    (hker : ∀ z : M, f z = 0 → σ • z = z →
      ∃ c : M, f c = 0 ∧ ∑ i ∈ Finset.range n, σ ^ i • c = z)
    (d : D) (m : M) (hm : σ • d - d = f m) :
    ∃ y : M, σ • (d - f y) = d - f y := by
  have hfpow (i : ℕ) (x : M) : f (σ ^ i • x) = σ ^ i • f x := by
    induction i with
    | zero => simp only [pow_zero, one_smul]
    | succ i ih => rw [pow_succ', mul_smul, hf, ih, mul_smul]
  let N := ∑ i ∈ Finset.range n, σ ^ i • m
  have hNker : f N = 0 := by
    change f (∑ i ∈ Finset.range n, σ ^ i • m) = 0
    rw [map_sum]
    simp only [hfpow, ← hm]
    rw [sum_range_smul_sub, hD, sub_self]
  have hNfixed : σ • N = N := by
    apply sub_eq_zero.mp
    exact (smul_sum_range_sub σ n m).trans (by rw [hM, sub_self])
  obtain ⟨c, hc, hNc⟩ := hker N hNker hNfixed
  have hzero : ∑ i ∈ Finset.range n, σ ^ i • (m - c) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hNc]
    exact sub_self N
  obtain ⟨y, hy⟩ := h90 (m - c) hzero
  refine ⟨y, sub_eq_zero.mp ?_⟩
  have hfy : σ • f y - f y = f (m - c) := by
    rw [← hf, ← map_sub, hy]
  calc
    σ • (d - f y) - (d - f y) = (σ • d - d) - (σ • f y - f y) := by
      rw [smul_sub]
      abel
    _ = f m - f (m - c) := by rw [hm, hfy]
    _ = 0 := by rw [map_sub, hc, sub_zero, sub_self]

end CyclicAction
