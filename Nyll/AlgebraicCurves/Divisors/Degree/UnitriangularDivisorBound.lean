/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Degree.FiniteTypePoleBound
import Nyll.ValuedFieldTheory.Valuation.UnitriangularPoleBound

/-! # Actual divisor bounds for products of unitriangular rational matrices

The uniform matrix valuation estimate gives an order bound at each actual place.
Finite support of principal divisors then gives a single effective divisor that
bounds every product of matrices drawn from a prescribed finite family, even
when factors repeat arbitrarily often. This is the pole estimate in the
unipotent part of Serre's modulus-existence proof, not the reciprocity statement.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

private theorem adicValuation_le_exp_nat_iff (v : Place K F) (b : ℕ) (f : F) :
    v.adicValuation f ≤ WithZero.exp (b : ℤ) ↔ -(b : ℤ) ≤ v.ord f := by
  by_cases hf : f = 0
  · subst f
    rw [map_zero, v.ord_zero]
    exact iff_of_true zero_le (neg_nonpos.mpr (Int.natCast_nonneg b))
  · rw [← WithZero.log_le_iff_le_exp (v.adicValuation_ne_zero hf)]
    change WithZero.log (v.adicValuation f) ≤ (b : ℤ) ↔
      -(b : ℤ) ≤ -WithZero.log (v.adicValuation f)
    omega

/-- A product of upper unitriangular matrices with poles of order at most `b`
has poles of order at most `(r - 1) * b`, independently of the number of factors. -/
theorem ord_list_prod_unitriangular_ge (v : Place K F) {r : ℕ}
    (L : List (Matrix (Fin r) (Fin r) F)) (b : ℕ)
    (hL : ∀ A ∈ L, A.IsUpperTriangular)
    (hd : ∀ A ∈ L, ∀ i, A i i = 1)
    (hb : ∀ A ∈ L, ∀ i j, -(b : ℤ) ≤ v.ord (A i j)) (i j : Fin r) :
    -(((r - 1) * b : ℕ) : ℤ) ≤ v.ord (L.prod i j) := by
  have hc : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (b : ℤ) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    exact Int.natCast_nonneg b
  have hbound : ∀ A ∈ L, ∀ k l, v.adicValuation (A k l) ≤ WithZero.exp (b : ℤ) :=
    fun A hA k l => (v.adicValuation_le_exp_nat_iff b (A k l)).mpr (hb A hA k l)
  have h := v.adicValuation.map_list_prod_unitriangular_entry_le L hc hL hd hbound i j
  rw [← WithZero.exp_nsmul, nsmul_eq_mul] at h
  apply (v.adicValuation_le_exp_nat_iff ((r - 1) * b) (L.prod i j)).mp
  simpa only [Nat.cast_mul] using h

end Place

variable [HasPrincipalDivisors K F]

/-- One actual finite divisor bounds all products from a finite family of
unitriangular rational matrices. The length and repetitions of a product do not
alter the bound. -/
theorem exists_unitriangular_product_divisor_bound {ι : Type*} {r : ℕ}
    (S : Finset ι) (A : ι → Matrix (Fin r) (Fin r) F)
    (hA : ∀ a ∈ S, (A a).IsUpperTriangular)
    (hd : ∀ a ∈ S, ∀ i, A a i i = 1) :
    ∃ D : Modulus K F, ∀ v : Place K F, ∀ L : List ι,
      (∀ a ∈ L, a ∈ S) → ∀ i j : Fin r,
        -(((r - 1) * D v : ℕ) : ℤ) ≤ v.ord ((L.map A).prod i j) := by
  classical
  let I : Finset (ι × (Fin r × Fin r)) := S.product (Finset.univ.product Finset.univ)
  obtain ⟨D, hD, _⟩ := exists_finset_pole_bound (K := K) I
    (fun a : ι × (Fin r × Fin r) => A a.1 a.2.1 a.2.2)
  refine ⟨D, ?_⟩
  intro v L hL i j
  apply v.ord_list_prod_unitriangular_ge (L.map A) (D v)
  · intro B hB
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hB
    exact hA a (hL a ha)
  · intro B hB k
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hB
    exact hd a (hL a ha) k
  · intro B hB k l
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hB
    apply hD v (a, k, l)
    exact Finset.mem_product.mpr ⟨hL a ha,
      Finset.mem_product.mpr ⟨Finset.mem_univ k, Finset.mem_univ l⟩⟩

end AlgebraicCurve
