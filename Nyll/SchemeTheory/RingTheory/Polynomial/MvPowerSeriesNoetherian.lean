/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPowerSeries_isNoetherianRing_of_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPowerSeries_isNoetherianRing_fin.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Noetherianity of formal power series in finitely many variables

Use Mathlib's canonical instance for a finite variable type.
-/

section MvPowerSeries_isNoetherianRing_of_finite

universe u v

theorem _root_.MvPowerSeries.isNoetherianRing_of_finite {σ : Type u} {R : Type v} [Finite σ]
  [CommRing R]
    [IsNoetherianRing R] : IsNoetherianRing (MvPowerSeries σ R) :=
  inferInstance

end MvPowerSeries_isNoetherianRing_of_finite



section MvPowerSeries_isNoetherianRing_fin

theorem MvPowerSeries.isNoetherianRing_fin
    (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) :=
  inferInstance

end MvPowerSeries_isNoetherianRing_fin
