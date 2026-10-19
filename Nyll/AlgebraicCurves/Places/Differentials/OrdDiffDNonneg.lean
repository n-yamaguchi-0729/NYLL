/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_D_nonneg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Differentials.DifferentialOrder
import Nyll.AlgebraicCurves.Places.Differentials.OrdDiffCoeffDNonneg

/-!
# Place ord Diff D nonneg
-/

namespace AlgebraicCurve.Place

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
theorem ordDiff_D_nonneg (v : Place K F) {f : F} (hf : 0 ≤ v.ord f) : 0 ≤ v.ordDiff (D K F f) := by
  obtain ⟨t, ht⟩ := v.exists_ord_eq_one
  rw [ordDiff_eq_ord_diffCoeff x v ht]
  exact Place.ord_diffCoeff_D_nonneg x v ht hf

end AlgebraicCurve.Place
