/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Nyll.AlgebraicCurves.Divisors.Maps.Maps

/-!
# Existence of the restriction of a place
-/

theorem _root_.AlgebraicCurve.Place.exists_toValuationSubring_eq_comap {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : AlgebraicCurve.Place K F') :
    ∃ v : AlgebraicCurve.Place K F,
      v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F') :=
  ⟨w.restrict F, AlgebraicCurve.Place.restrict_toValuationSubring w⟩
