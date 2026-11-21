/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.NormTrace.EvalAtTraceEqSumFiber
public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Places.ValuationRings.IntegralClosureAtOrdFiberNonneg
public import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegEqOneIsRational
public import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqRamificationIdxFiberCenter
public import Nyll.AlgebraicCurves.Places.Degree.FinrankPrimePow
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Trace.Quotient
public import Nyll.AlgebraicCurves.Differentials.Basic

/-!
# Place mem and eval At trace eq sum ramification Index Along smul eval At
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

open _root_.AlgebraicCurve _root_.AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong
      k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ
      = x)
    (g : F') (hg : ∀ y ∈ S, g ∈ y.toValuationSubring) :
    let := AlgebraicCurve.algebraAlong φ
    Algebra.trace F F' g ∈ x.toValuationSubring ∧
      x.evalAt (Algebra.trace F F' g) = ∑ y ∈ S, ((Place.ramificationIndexAlong φ y : ℕ) : k) •
        y.evalAt g := by
  intro sharedOwner1
  classical
  have := AlgebraicCurve.isScalarTower_along φ
  have := AlgebraicCurve.isIntegral_along φ hφ
  have : FiniteDimensional F F' := hfin
  have : Algebra.IsSeparable F F' := hsep
  have : HasPrincipalDivisors k F' := IsCurveOver.hasPrincipalDivisors
  have hratF' : ∀ w : Place k F', w.IsRational := fun w =>
    (Place.isRational_iff_deg_eq_one w).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed w)
  have hx : x.IsRational := (Place.isRational_iff_deg_eq_one x).mpr
    (IsCurveOver.deg_eq_one_of_isAlgClosed x)
  have hSfib : S = x.fiber F' := by
    ext y
    rw [hS y, Place.mem_fiber]
    rfl
  by_cases hg0 : g = 0
  · subst hg0
    refine ⟨by rw [map_zero]; exact zero_mem _, ?_⟩
    have hx0 : x.evalAt (0 : F) = 0 := by
      simpa only [map_zero] using x.evalAt_algebraMap (0 : k)
    rw [map_zero, hx0]
    symm
    apply Finset.sum_eq_zero
    intro y _
    have hy0 : y.evalAt (0 : F') = 0 := by
      simpa only [map_zero] using y.evalAt_algebraMap (0 : k)
    rw [hy0, smul_zero]
  obtain ⟨hmem, hval⟩ := x.mem_and_evalAt_trace_eq_sum_fiber hx (fun w _ => hratF' w) g hg0
    (fun w hw => Place.ord_nonneg_of_mem w (hg w (hSfib ▸ hw)))
  refine ⟨hmem, ?_⟩
  rw [hval, hSfib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Nat.cast_smul_eq_nsmul]
  rfl
end
end Place_mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt
end AlgebraicCurves.Places.Proofs
end ProofImplementation
