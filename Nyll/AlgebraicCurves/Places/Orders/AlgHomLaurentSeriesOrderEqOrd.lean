/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_algHom_laurentSeries_order_eq_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.Degree.AlgHomLaurentSeriesDegEqOne

/-!
# Place exists alg Hom laurent Series order eq ord
-/

namespace AlgebraicCurve.Place

theorem exists_algHom_laurentSeries_order_eq_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.deg = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K, ∀ x : F, (φ x).order = w.ord x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨φ, _, hφ⟩ :=
    w.exists_algHom_laurentSeries_of_deg_eq_one hw (π : F) (w.ord_coe_irreducible hπ)
  exact ⟨φ, hφ⟩

end AlgebraicCurve.Place
