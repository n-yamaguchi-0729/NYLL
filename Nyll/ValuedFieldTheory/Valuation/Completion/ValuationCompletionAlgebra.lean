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

import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Mathlib.Topology.Algebra.UniformRing

/-!
# Valuation Completion Algebra
-/

noncomputable section

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

@[simp] theorem algebraMap_completion_apply (a : K) :
    algebraMap K v.Completion a = (a : v.Completion) := rfl

theorem smul_completion_def (a : K) (x : v.Completion) : a • x = (a : v.Completion) * x :=
  Algebra.smul_def a x

end Valuation

end
