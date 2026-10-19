/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Valuation.Basic

/-! # A uniform pole bound for products of unitriangular matrices

If every entry of every upper unitriangular matrix has valuation at most `c ≥ 1`,
every entry of their product has valuation at most `c ^ (r - 1)`. The bound does
not depend on the number of factors. More precisely, the `(i,j)` entry is bounded
by `c ^ (j - i)`. Weighted entry bounds are preserved by matrix multiplication.

This proves the local matrix estimate in Serre, *Algebraic Groups and Class Fields*,
Chapter III, §2, Lemma 8 (pp. 44–45). It does not assume or assert an embedding of
an arbitrary algebraic group into a unitriangular group.
-/

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {r : ℕ} {c : Γ₀}

private theorem weighted_upper_mul {A B : Matrix (Fin r) (Fin r) R}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (ha : ∀ i j, v (A i j) ≤ c ^ (j.val - i.val))
    (hb : ∀ i j, v (B i j) ≤ c ^ (j.val - i.val)) :
    ∀ i j, v ((A * B) i j) ≤ c ^ (j.val - i.val) := by
  intro i j
  rw [Matrix.mul_apply]
  apply v.map_sum_le
  intro k _
  by_cases hik : i ≤ k
  · by_cases hkj : k ≤ j
    · rw [v.map_mul]
      calc
        v (A i k) * v (B k j) ≤ c ^ (k.val - i.val) * c ^ (j.val - k.val) :=
          mul_le_mul' (ha i k) (hb k j)
        _ = c ^ (j.val - i.val) := by
          rw [← pow_add]
          congr 1
          omega
    · rw [hB (lt_of_not_ge hkj), mul_zero, v.map_zero]
      exact zero_le
  · rw [hA (lt_of_not_ge hik), zero_mul, v.map_zero]
    exact zero_le

private theorem weighted_upper_of_bound {A : Matrix (Fin r) (Fin r) R}
    (hc : 1 ≤ c) (hA : A.IsUpperTriangular)
    (hd : ∀ i, v (A i i) ≤ 1) (ha : ∀ i j, v (A i j) ≤ c) :
    ∀ i j, v (A i j) ≤ c ^ (j.val - i.val) := by
  intro i j
  by_cases hji : j < i
  · rw [hA hji, v.map_zero]
    exact zero_le
  · by_cases hij : i = j
    · subst j
      rw [Nat.sub_self, pow_zero]
      exact hd i
    · calc
        v (A i j) ≤ c := ha i j
        _ = c ^ 1 := (pow_one c).symm
        _ ≤ c ^ (j.val - i.val) := pow_le_pow_right' hc (by omega)

private theorem weighted_upper_list_prod (L : List (Matrix (Fin r) (Fin r) R))
    (hL : ∀ A ∈ L, A.IsUpperTriangular)
    (hb : ∀ A ∈ L, ∀ i j, v (A i j) ≤ c ^ (j.val - i.val)) :
    L.prod.IsUpperTriangular ∧ ∀ i j, v (L.prod i j) ≤ c ^ (j.val - i.val) := by
  induction L with
  | nil =>
    rw [List.prod_nil]
    refine ⟨Matrix.blockTriangular_one, ?_⟩
    intro i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.one_apply_eq, v.map_one, Nat.sub_self, pow_zero]
    · rw [Matrix.one_apply_ne hij, v.map_zero]
      exact zero_le
  | cons A L ih =>
    have hA : A.IsUpperTriangular := hL A (List.mem_cons_self)
    have htail : ∀ B ∈ L, B.IsUpperTriangular :=
      fun B hB => hL B (List.mem_cons_of_mem A hB)
    have hbound : ∀ B ∈ L, ∀ i j, v (B i j) ≤ c ^ (j.val - i.val) :=
      fun B hB => hb B (List.mem_cons_of_mem A hB)
    obtain ⟨hp, hpb⟩ := ih htail hbound
    rw [List.prod_cons]
    exact ⟨hA.mul hp, v.weighted_upper_mul hA hp (hb A List.mem_cons_self) hpb⟩

/-- Products of bounded upper triangular matrices with integral diagonal entries
have a bound depending only on the distance above the diagonal. -/
theorem map_list_prod_upperTriangular_entry_le
    (L : List (Matrix (Fin r) (Fin r) R)) (hc : 1 ≤ c)
    (hL : ∀ A ∈ L, A.IsUpperTriangular)
    (hd : ∀ A ∈ L, ∀ i, v (A i i) ≤ 1)
    (hb : ∀ A ∈ L, ∀ i j, v (A i j) ≤ c) (i j : Fin r) :
    v (L.prod i j) ≤ c ^ (j.val - i.val) :=
  (v.weighted_upper_list_prod L hL
    (fun A hA => v.weighted_upper_of_bound hc (hL A hA) (hd A hA) (hb A hA))).2 i j

/-- Serre's uniform bound for a product of any number of upper unitriangular
matrices. The exponent depends on matrix size, not on the number of factors. -/
theorem map_list_prod_unitriangular_entry_le
    (L : List (Matrix (Fin r) (Fin r) R)) (hc : 1 ≤ c)
    (hL : ∀ A ∈ L, A.IsUpperTriangular)
    (hd : ∀ A ∈ L, ∀ i, A i i = 1)
    (hb : ∀ A ∈ L, ∀ i j, v (A i j) ≤ c) (i j : Fin r) :
    v (L.prod i j) ≤ c ^ (r - 1) := by
  have hdiag : ∀ A ∈ L, ∀ i, v (A i i) ≤ 1 := by
    intro A hA k
    rw [hd A hA k, v.map_one]
  exact (v.map_list_prod_upperTriangular_entry_le L hc hL hdiag hb i j).trans
    (pow_le_pow_right' hc (by omega))

/-- The same uniform bound for the original `1 + N` form, where every `N`
is strictly upper triangular. No commutation of the matrices is required. -/
theorem map_list_prod_one_add_strictUpper_entry_le
    (L : List (Matrix (Fin r) (Fin r) R)) (hc : 1 ≤ c)
    (hL : ∀ N ∈ L, ∀ i j, j ≤ i → N i j = 0)
    (hb : ∀ N ∈ L, ∀ i j, v (N i j) ≤ c) (i j : Fin r) :
    v ((L.map (fun N => (1 : Matrix (Fin r) (Fin r) R) + N)).prod i j) ≤ c ^ (r - 1) := by
  apply v.map_list_prod_unitriangular_entry_le _ hc
  · intro A hA
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hA
    intro k l hlk
    change l < k at hlk
    change (1 : Matrix (Fin r) (Fin r) R) k l + N k l = 0
    rw [Matrix.one_apply_ne (ne_of_gt hlk), hL N hN k l hlk.le, zero_add]
  · intro A hA k
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hA
    rw [Matrix.add_apply, Matrix.one_apply_eq, hL N hN k k le_rfl, add_zero]
  · intro A hA k l
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hA
    rw [Matrix.add_apply]
    apply v.map_add_le _ (hb N hN k l)
    by_cases hkl : k = l
    · subst l
      rw [Matrix.one_apply_eq, v.map_one]
      exact hc
    · rw [Matrix.one_apply_ne hkl, v.map_zero]
      exact zero_le

end Valuation
