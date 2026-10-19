/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.MemRiemannRochSpaceHasValueZpowMul
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions

/-!
# Nonvanishing in a rational Riemann–Roch space

Use the existing exact-order construction at a place to avoid the smaller divisor space.
-/

namespace AlgebraicCurve

open AlgebraicCurves.Cohomology.RiemannRoch.Proofs
open ExistsMemRRSpaceAllHasValueZpow.AlgebraicCurve.RationalFunctionField

theorem exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : 0 ≤ E.degree) (w : Place k F) :
    ∃ p ∈ riemannRochSpace E, p ∉ riemannRochSpace (E - Finsupp.single w 1) := by
  classical
  obtain ⟨p, hp, hp0, hord⟩ := exists_mem_riemannRochSpace_ord_eq_of_ringEquiv e he E hE w
  refine ⟨p, hp, fun h => ?_⟩
  rcases (mem_riemannRochSpace_iff.mp h) w with h0 | hle
  · exact hp0 h0
  · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at hle
    omega

end AlgebraicCurve
