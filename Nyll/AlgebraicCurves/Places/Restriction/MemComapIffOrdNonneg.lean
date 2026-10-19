/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mem_comap_iff_ord_nonneg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place mem comap iff ord nonneg
-/

open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.mem_comap_iff_ord_nonneg {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F'] [Algebra F F'] {w : Place K F'} {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  rw [ValuationSubring.mem_comap]
  exact w.mem_iff_ord_nonneg ((map_ne_zero (algebraMap F F')).mpr hf)
