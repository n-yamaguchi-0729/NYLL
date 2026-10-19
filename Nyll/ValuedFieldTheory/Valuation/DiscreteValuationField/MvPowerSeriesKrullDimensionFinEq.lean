/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2025 Andrew Yang. All rights reserved.
Authors: Andrew Yang, Kevin Buzzard, Michael Rothgang
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Patching/Utils/Depth.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.RegularLocal.ModuleDepthRegularQuotient
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Dimension of formal power series over a discrete valuation ring

Separating one variable gives an ordinary power series ring, whose dimension is one
more than that of its coefficient ring. Induction starts at the discrete valuation ring.
-/

open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq

theorem MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) 𝓞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
  induction n with
  | zero =>
      rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) 𝓞).toRingEquiv]
      exact IsPrincipalIdealRing.ringKrullDim_eq_one 𝓞
        (IsDiscreteValuationRing.not_isField 𝓞)
  | succ n ih =>
      rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv 𝓞 n).toRingEquiv,
        Ws14Port.PowerSeries.ringKrullDim_powerSeries, ih]
      simp only [Nat.cast_add, Nat.cast_one]
