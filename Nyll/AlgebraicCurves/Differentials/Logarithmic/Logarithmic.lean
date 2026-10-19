/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Places.Basic

/-!
# Logarithmic
-/

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The logarithmic differential `df / f`. -/
def dlog (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (f : F) :
    Ω[F⁄K] :=
  f⁻¹ • KaehlerDifferential.D K F f
@[simp]
theorem dlog_zero : dlog K (0 : F) = 0 := by
  rw [dlog, map_zero, smul_zero]
@[simp]
theorem dlog_one : dlog K (1 : F) = 0 := by
  rw [dlog, Derivation.map_one_eq_zero, smul_zero]

theorem dlog_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    dlog K (f * g) = dlog K f + dlog K g := by
  rw [dlog, dlog, dlog, Derivation.leibniz, smul_add,
    smul_smul, smul_smul, mul_inv]
  rw [show f⁻¹ * g⁻¹ * f = g⁻¹ by field_simp,
    show f⁻¹ * g⁻¹ * g = f⁻¹ by field_simp, add_comm]

theorem dlog_pow (n : ℕ) {f : F} (hf : f ≠ 0) :
    dlog K (f ^ n) = n • dlog K f := by
  induction n with
  | zero => rw [pow_zero, dlog_one, zero_nsmul]
  | succ k ih =>
      rw [pow_succ, dlog_mul (pow_ne_zero k hf) hf, ih, succ_nsmul]

theorem dlog_pow_char (ℓ : ℕ) [CharP F ℓ] {f : F} (hf : f ≠ 0) :
    dlog K (f ^ ℓ) = 0 := by
  rw [dlog_pow ℓ hf, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F ℓ, zero_smul]

section Regular

variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]

/-- Differentials regular at every place. -/
def regularDifferentialsOfNonnegativeOrder (K F : Type*) [Field K] [Field F] [Algebra K F]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]] : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, 0 ≤ v.ordDifferential ω}
  zero_mem' := by
    intro v
    rw [Place.ordDifferential, v.differentialCoeff_zero, v.ord_zero]
  add_mem' := by
    intro ω ω' hω hω' v
    rw [Place.ordDifferential, Place.differentialCoeff_add]
    have h₁ : v.differentialCoeff ω ∈ v.toValuationSubring :=
      Place.mem_toValuationSubring_of_ord_nonneg v (hω v)
    have h₂ : v.differentialCoeff ω' ∈ v.toValuationSubring :=
      Place.mem_toValuationSubring_of_ord_nonneg v (hω' v)
    exact v.ord_nonneg_of_mem (add_mem h₁ h₂)
  smul_mem' := by
    intro a ω hω v
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul, Place.ordDifferential, v.differentialCoeff_zero, v.ord_zero]
    have hsmul : a • ω = (algebraMap K F a) • ω := (algebraMap_smul F a ω).symm
    rw [Place.ordDifferential, hsmul, v.differentialCoeff_smul]
    rcases eq_or_ne (v.differentialCoeff ω) 0 with hc | hc
    · rw [hc, mul_zero, v.ord_zero]
    have hmap : algebraMap K F a ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K F).injective).mpr ha
    rw [v.ord_mul hmap hc, v.ord_algebraMap a, zero_add]
    exact hω v
@[simp]
theorem mem_regularDifferentialsOfNonnegativeOrder_iff {ω : Ω[F⁄K]} :
    ω ∈ regularDifferentialsOfNonnegativeOrder K F
      ↔ ∀ v : Place K F, 0 ≤ v.ordDifferential ω :=
  Iff.rfl

end Regular

end AlgebraicCurve

end
