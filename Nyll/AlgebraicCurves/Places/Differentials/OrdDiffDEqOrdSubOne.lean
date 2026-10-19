/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Places.Taylor.DerivationCoefficients
import Nyll.AlgebraicCurves.Places.Differentials.DifferentialOrder
import Nyll.AlgebraicCurves.Places.Differentials.OrdDiffCoeffDNonneg
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR

/-!
# Place ord Diff D eq ord sub one
-/

namespace AlgebraicCurve.Place

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
private theorem ordDiff_D_of_ord_pos (v : Place K F) {f : F} (hf : 0 < v.ord f) :
    v.ordDiff (D K F f) = v.ord f - 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπord : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hπ0 : v.ord (π : F) ≠ 0 := by rw [hπord]; exact one_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at hf
    exact (lt_irrefl 0) hf
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v.ord f = n := ⟨(v.ord f).toNat, (Int.toNat_of_nonneg hf.le).symm⟩
  have hn0 : n ≠ 0 := by
    intro hn0
    rw [hn, hn0, Nat.cast_zero] at hf
    exact (lt_irrefl 0) hf
  rw [hn, zpow_natCast] at hu
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  set uF : F := ((u : v.toValuationSubring) : F) with huF
  have huF0 : uF ≠ 0 := by
    intro h; apply hf0; rw [hu, h, zero_mul]
  have hπF : (π : F) ≠ 0 := by
    intro h; rw [h, v.ord_zero] at hπord; exact zero_ne_one hπord
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have huord : v.ord uF = 0 := v.ord_coe_unit u
  set cu := Place.diffCoeff (π : F) (D K F uF) with hcu
  have hcu_ge : 0 ≤ v.ord cu := Place.ord_diffCoeff_D_nonneg x v hπord huord.ge
  have hDu : cu • D K F (π : F) = D K F uF := Place.diffCoeff_smul_D_of_ord_ne_zero x v hπ0 _
  have hDf : D K F f = (uF * (n * (π : F) ^ (n - 1)) + (π : F) ^ n * cu) • D K F (π : F) := by
    rw [hu, Derivation.leibniz, Derivation.leibniz_pow, ← hDu, ← Nat.cast_smul_eq_nsmul F]
    simp only [smul_smul]
    rw [← add_smul]
  rw [ordDiff_eq_ord_diffCoeff x v hπord, hDf, Place.diffCoeff_smul_D_eq x v hπ0, hn]
  have hπn1 : v.ord ((π : F) ^ (n - 1)) = ((n - 1 : ℕ) : ℤ) := by
    rw [← zpow_natCast, v.ord_zpow, hπord, mul_one]
  have hA0 : uF * (n * (π : F) ^ (n - 1)) ≠ 0 :=
    mul_ne_zero huF0 (mul_ne_zero hnF (pow_ne_zero _ hπF))
  have hA : v.ord (uF * (n * (π : F) ^ (n - 1))) = ((n - 1 : ℕ) : ℤ) := by
    rw [v.ord_mul huF0 (mul_ne_zero hnF (pow_ne_zero _ hπF)), huord, zero_add,
      v.ord_mul hnF (pow_ne_zero _ hπF), v.ord_natCast n, zero_add, hπn1]
  have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one]
  rcases eq_or_ne cu 0 with hcu0 | hcu0
  · rw [hcu0, mul_zero, add_zero, hA, hsub]
  · have hB : v.ord ((π : F) ^ n * cu) = (n : ℤ) + v.ord cu := by
      rw [v.ord_mul (pow_ne_zero _ hπF) hcu0, ← zpow_natCast, v.ord_zpow, hπord, mul_one]
    rw [Place.ord_add_eq_of_lt v hA0 (mul_ne_zero (pow_ne_zero _ hπF) hcu0)
      (by rw [hA, hB, hsub]; omega), hA, hsub]

include x in
theorem ordDiff_D_eq_ord_sub_one (v : Place K F) {f : F} (hf : v.ord f ≠ 0) :
    v.ordDiff (D K F f) = v.ord f - 1 := by
  rcases lt_or_gt_of_ne hf with hneg | hpos
  · have hf0 : f ≠ 0 := by
      rintro rfl
      rw [v.ord_zero] at hneg
      exact (lt_irrefl 0) hneg
    have hinv : 0 < v.ord f⁻¹ := by rw [v.ord_inv]; omega
    have hinv0 : v.ord f⁻¹ ≠ 0 := hinv.ne'
    have hDf : D K F f = (-(f ^ 2)) • D K F f⁻¹ := by
      rw [Derivation.leibniz_inv, smul_smul]
      have : -(f ^ 2) * -(f⁻¹ ^ 2) = 1 := by
        rw [neg_mul_neg, ← mul_pow, mul_inv_cancel₀ hf0, one_pow]
      rw [this, one_smul]
    rw [hDf, ordDiff_smul x v (neg_ne_zero.mpr (pow_ne_zero 2 hf0))
      (Place.D_ne_zero_of_ord_ne_zero x v hinv0), ordDiff_D_of_ord_pos x v hinv, v.ord_neg,
      ← zpow_natCast, v.ord_zpow, v.ord_inv]
    push_cast
    ring
  · exact ordDiff_D_of_ord_pos x v hpos

end AlgebraicCurve.Place
