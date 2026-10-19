/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.TameUniformizerNormalization
import Mathlib.RingTheory.LaurentSeries

/-! # Order-preserving tame normalization of the entire Laurent field

The constructed power-series parameter change extends through the fraction
ring and preserves every Laurent order, including poles.
-/

noncomputable section

namespace LaurentSeries

variable {K : Type*} [Field K]

private theorem order_coe_powerSeries (f : PowerSeries K) :
    (f : LaurentSeries K).order = (f.order.toNat : ℤ) := by
  by_cases hf : f = 0
  · subst f
    simp only [PowerSeries.coe_zero, HahnSeries.order_zero, PowerSeries.order_zero,
      ENat.toNat_top, Nat.cast_zero]
  have hf' : (f : LaurentSeries K) ≠ 0 := by
    intro h
    apply hf
    exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  have hc : (f : LaurentSeries K).coeff (f.order.toNat : ℤ) ≠ 0 := by
    rw [coeff_coe_powerSeries]
    exact PowerSeries.coeff_order hf
  have hlead : (f : LaurentSeries K).coeff (f : LaurentSeries K).order ≠ 0 :=
    HahnSeries.coeff_order_eq_zero.not.mpr hf'
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra h
  have hlt : (f : LaurentSeries K).order < (f.order.toNat : ℤ) := lt_of_not_ge h
  by_cases hneg : (f : LaurentSeries K).order < 0
  · apply hlead
    simp only [PowerSeries.coeff_coe, hneg, ↓reduceIte]
  · have hnonneg : 0 ≤ (f : LaurentSeries K).order := le_of_not_gt hneg
    have hcast := Int.eq_natAbs_of_nonneg hnonneg
    have hsmall : (f : LaurentSeries K).order.natAbs < f.order.toNat := by omega
    apply hlead
    simpa only [PowerSeries.coeff_coe, hneg, ↓reduceIte] using
      PowerSeries.coeff_of_lt_order_toNat (f : LaurentSeries K).order.natAbs hsmall

/-- An order-preserving parameter automorphism of the power-series ring
extends to an order-preserving automorphism of its entire fraction field. -/
theorem exists_orderPreservingExtension
    (E : PowerSeries K ≃ₐ[K] PowerSeries K)
    (hE : ∀ A, (E A).order = A.order) :
    ∃ E' : LaurentSeries K ≃ₐ[K] LaurentSeries K,
      (∀ A : PowerSeries K, E' (A : LaurentSeries K) = (E A : LaurentSeries K)) ∧
      ∀ z, (E' z).order = z.order := by
  have htower := IsScalarTower.of_algebraMap_eq
    (R := K) (S := PowerSeries K) (A := LaurentSeries K)
    (fun _ => rfl)
  let E' : LaurentSeries K ≃ₐ[K] LaurentSeries K :=
    IsFractionRing.algEquivOfAlgEquiv E
  have hmap (A : PowerSeries K) :
      E' (A : LaurentSeries K) = (E A : LaurentSeries K) :=
    IsFractionRing.algEquivOfAlgEquiv_algebraMap E A
  refine ⟨E', hmap, ?_⟩
  have hcoe (A : PowerSeries K) :
      (E' (A : LaurentSeries K)).order = (A : LaurentSeries K).order := by
    rw [hmap, order_coe_powerSeries, hE, order_coe_powerSeries]
  intro z
  by_cases hz : z = 0
  · subst z
    rw [map_zero]
  obtain ⟨A, B, hB, hfrac⟩ := IsFractionRing.div_surjective (PowerSeries K) z
  have hB' : (B : LaurentSeries K) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hB
  have hmul : z * (B : LaurentSeries K) = (A : LaurentSeries K) := by
    rw [← hfrac]
    exact div_mul_cancel₀ _ hB'
  have hEz : E' z ≠ 0 := by
    intro h
    exact hz (E'.injective (h.trans (map_zero E').symm))
  have hEB : E' (B : LaurentSeries K) ≠ 0 := by
    intro h
    exact hB' (E'.injective (h.trans (map_zero E').symm))
  have hmul' := congrArg E' hmul
  rw [map_mul] at hmul'
  have ho := congrArg HahnSeries.order hmul
  have ho' := congrArg HahnSeries.order hmul'
  rw [HahnSeries.order_mul hz hB'] at ho
  rw [HahnSeries.order_mul hEz hEB, hcoe B, hcoe A] at ho'
  exact add_right_cancel (ho'.trans ho.symm)

/-- The entire positive-order tame Laurent series is normalized to a pure
monomial by an automorphism preserving the order of every Laurent series. -/
theorem exists_tameNormalization [IsAlgClosed K]
    (f : LaurentSeries K) (e : ℕ) (he : (e : K) ≠ 0)
    (horder : f.order = (e : ℤ)) :
    ∃ E : LaurentSeries K ≃ₐ[K] LaurentSeries K,
      E f = HahnSeries.single (e : ℤ) (1 : K) ∧
      ∀ A, (E A).order = A.order := by
  have he0 : e ≠ 0 := by
    intro h
    exact he (h ▸ Nat.cast_zero)
  have hf : f ≠ 0 := by
    intro h
    rw [h, HahnSeries.order_zero] at horder
    exact he0 (by exact_mod_cast horder.symm)
  let P : PowerSeries K := PowerSeries.X ^ e * f.powerSeriesPart
  have hP : (P : LaurentSeries K) = f :=
    X_order_mul_powerSeriesPart horder.symm
  have hP0 : P ≠ 0 := by
    intro h
    apply hf
    rw [← hP, h, PowerSeries.coe_zero]
  have hPn : P.order.toNat = e := by
    have ho := (order_coe_powerSeries P).symm.trans
      ((congrArg HahnSeries.order hP).trans horder)
    exact_mod_cast ho
  have hPo : P.order = (e : ℕ∞) := by
    rw [← PowerSeries.coe_toNat_order hP0, hPn]
  obtain ⟨E, hEP, hE⟩ := PowerSeries.exists_tameNormalization P e he hPo
  obtain ⟨E', hE', horder'⟩ := exists_orderPreservingExtension E hE
  refine ⟨E', ?_, horder'⟩
  calc
    E' f = E' (P : LaurentSeries K) := congrArg E' hP.symm
    _ = (E P : LaurentSeries K) := hE' P
    _ = ((PowerSeries.X ^ e : PowerSeries K) : LaurentSeries K) :=
      congrArg (fun A : PowerSeries K => (A : LaurentSeries K)) hEP
    _ = HahnSeries.single (e : ℤ) (1 : K) := HahnSeries.ofPowerSeries_X_pow e

end LaurentSeries
