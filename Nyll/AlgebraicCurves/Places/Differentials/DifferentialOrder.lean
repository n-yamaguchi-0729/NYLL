/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_smul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_smul_of_perfectField.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_zero.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential_of_perfectField.lean
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Places.Taylor.DerivationCoefficients
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Differentials.OrdDiffCoeffDNonneg
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialSpanDEqTop
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialDNeZero
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.IsAlgebraicAdjoinTranscendental
import Nyll.AlgebraicCurves.Places.Orders.TranscendentalOrdNeZero
import Mathlib.FieldTheory.Perfect
import Nyll.AlgebraicCurves.Places.Orders.SeparableAdjoinOrdEqOne
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry
import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveIffTranscendentalFiniteDimensional
import Nyll.AlgebraicCurves.Differentials.Regular.Regular
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
import Nyll.AlgebraicCurves.Places.Differentials.OrdDiffCoeffDNonnegPerfectField

/-!
# Place ord Diff eq ord diff Coeff
-/

section

namespace AlgebraicCurve.Place

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
private theorem ord_diffCoeff_D_eq_zero (v : Place K F) {t t' : F}
    (ht : v.ord t = 1) (ht' : v.ord t' = 1) :
    v.ord (Place.diffCoeff t (D K F t')) = 0 := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  have ht0' : v.ord t' ≠ 0 := by rw [ht']; exact one_ne_zero
  set c := Place.diffCoeff t (D K F t') with hc
  set c' := Place.diffCoeff t' (D K F t) with hc'
  have h1 : c • D K F t = D K F t' := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht0 _
  have h2 : c' • D K F t' = D K F t := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht0' _
  have hcc : c * c' = 1 := by
    have h3 : (c * c') • D K F t' = (1 : F) • D K F t' := by
      rw [one_smul, ← smul_smul, h2, h1]
    exact smul_left_injective F (Place.D_ne_zero_of_ord_ne_zero x v ht0') h3
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hc0' : c' ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  have hsum : v.ord c + v.ord c' = 0 := by rw [← v.ord_mul hc0 hc0', hcc, v.ord_one]
  have hge : 0 ≤ v.ord c := Place.ord_diffCoeff_D_nonneg x v ht (by rw [ht']; exact zero_le_one)
  have hge' : 0 ≤ v.ord c' := Place.ord_diffCoeff_D_nonneg x v ht' (by rw [ht]; exact zero_le_one)
  omega

include x in
theorem ordDiff_eq_ord_diffCoeff (v : Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ord (Place.diffCoeff t ω) := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  have hu : v.ord v.orderUniformizer = 1 := v.ord_orderUniformizer v.exists_ord_eq_one
  have hu0 : v.ord v.orderUniformizer ≠ 0 := by rw [hu]; exact one_ne_zero
  set a := Place.diffCoeff t ω with ha
  set c := Place.diffCoeff v.orderUniformizer (D K F t) with hc
  have hω : a • D K F t = ω := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht0 ω
  have hDt : c • D K F v.orderUniformizer = D K F t := Place.diffCoeff_smul_D_of_ord_ne_zero x v hu0
    _
  have hc0 : c ≠ 0 := by
    rintro h; rw [h, zero_smul] at hDt; exact Place.D_ne_zero_of_ord_ne_zero x v ht0 hDt.symm
  have hcord : v.ord c = 0 := ord_diffCoeff_D_eq_zero x v hu ht
  rw [Place.ordDiff_def, ← hω, ← hDt, smul_smul, Place.diffCoeff_smul_D_eq x v hu0]
  rcases eq_or_ne a 0 with h0 | ha0
  · rw [h0, zero_mul]
  · rw [v.ord_mul ha0 hc0, hcord, add_zero]

end AlgebraicCurve.Place

end

noncomputable section

open AlgebraicCurve AlgebraicCurve.Place KaehlerDifferential

theorem _root_.AlgebraicCurve.Place.ordDiff_smul_of_perfectField {K F : Type*} [Field K] [Field F]
  [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have ht : v.ord v.orderUniformizer = 1 := v.ord_orderUniformizer v.exists_ord_eq_one
  have hrep : diffCoeff v.orderUniformizer ω • KaehlerDifferential.D K F v.orderUniformizer = ω :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht ω
  have hgo : g • ω = (g * diffCoeff v.orderUniformizer ω) • KaehlerDifferential.D K F
    v.orderUniformizer := by
    conv_lhs => rw [← hrep]
    rw [smul_smul]
  have hco : diffCoeff v.orderUniformizer (g • ω) = g * diffCoeff v.orderUniformizer ω := by
    rw [hgo]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hc0 : diffCoeff v.orderUniformizer ω ≠ 0 := by
    intro h0
    apply hω
    rw [← hrep, h0, zero_smul]
  rw [ordDiff_def, ordDiff_def, hco, v.ord_mul hg hc0]

theorem _root_.AlgebraicCurve.Place.ordDiff_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
  [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  exact AlgebraicCurve.Place.ordDiff_smul_of_perfectField x v hg hω

theorem _root_.AlgebraicCurve.Place.ordDiff_zero_of_perfectField {K F : Type*} [Field K] [Field F]
  [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by
  have ht : v.ord v.orderUniformizer = 1 := v.ord_orderUniformizer v.exists_ord_eq_one
  have hcoeff := AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one x v ht (0 : F)
  rw [zero_smul] at hcoeff
  rw [AlgebraicCurve.Place.ordDiff_def, hcoeff, v.ord_zero]

theorem _root_.AlgebraicCurve.Place.ordDiff_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
  [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) :
    v.ordDiff 0 = 0 := by
  exact AlgebraicCurve.Place.ordDiff_zero_of_perfectField x v

theorem _root_.AlgebraicCurve.Place.ordDiff_eq_ordDifferential_of_perfectField {K F : Type*} [Field
  K]
    [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by
  obtain ⟨s, -, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K ({s} : Set F)) F := hfd
  have : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨π, hπ, hd⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have ht : v.ord v.orderUniformizer = 1 := v.ord_orderUniformizer ⟨π, hπ⟩
  rcases eq_or_ne ω 0 with rfl | hω
  · rw [Place.ordDiff_zero_of_perfectField s v, Place.ordDifferential, v.differentialCoeff_zero,
      v.ord_zero]
  have hf : v.differentialCoeff ω • D K F π = ω := by
    rw [← hd]
    exact v.differentialCoeff_smul_dCoord ω
  have hf0 : v.differentialCoeff ω ≠ 0 := by
    intro h
    apply hω
    rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]
  have hc : Place.diffCoeff v.orderUniformizer (D K F π) • D K F v.orderUniformizer = D K F π :=
    Place.diffCoeff_smul_D_of_ord_eq_one s v ht (D K F π)
  have hc' : Place.diffCoeff π (D K F v.orderUniformizer) • D K F π = D K F v.orderUniformizer :=
    Place.diffCoeff_smul_D_of_ord_eq_one s v hπ (D K F v.orderUniformizer)
  have hcc' : Place.diffCoeff v.orderUniformizer (D K F π) * Place.diffCoeff π (D K F
    v.orderUniformizer) = 1 := by
    have h1 := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v hπ
      (Place.diffCoeff v.orderUniformizer (D K F π) * Place.diffCoeff π (D K F v.orderUniformizer))
    rw [mul_smul, hc', hc] at h1
    have h2 := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v hπ (1 : F)
    rw [one_smul] at h2
    exact h1.symm.trans h2
  have hcn : 0 ≤ v.ord (Place.diffCoeff v.orderUniformizer (D K F π)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField s v ht (by rw [hπ]; norm_num)
  have hc'n : 0 ≤ v.ord (Place.diffCoeff π (D K F v.orderUniformizer)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField s v hπ (by rw [ht]; norm_num)
  have hc0 : Place.diffCoeff v.orderUniformizer (D K F π) ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
  have hc'0 : Place.diffCoeff π (D K F v.orderUniformizer) ≠ 0 := right_ne_zero_of_mul_eq_one hcc'
  have hsum := v.ord_mul hc0 hc'0
  rw [hcc', v.ord_one] at hsum
  have hcz : v.ord (Place.diffCoeff v.orderUniformizer (D K F π)) = 0 := by omega
  have hω' : (v.differentialCoeff ω * Place.diffCoeff v.orderUniformizer (D K F π)) • D K F
    v.orderUniformizer
      = ω := by
    rw [mul_smul, hc, hf]
  have hcoef := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v ht
    (v.differentialCoeff ω * Place.diffCoeff v.orderUniformizer (D K F π))
  rw [hω'] at hcoef
  rw [Place.ordDifferential, v.ordDiff_def, hcoef, v.ord_mul hf0 hc0, hcz, add_zero]

theorem _root_.AlgebraicCurve.Place.ordDiff_eq_ordDifferential {K F : Type*} [Field K] [Field F]
  [Algebra K F]
    [CharZero K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by
  exact AlgebraicCurve.Place.ordDiff_eq_ordDifferential_of_perfectField v ω

end
