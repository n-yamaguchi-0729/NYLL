/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqRamificationIdxFiberCenter
public import Nyll.AlgebraicCurves.Places.NormTrace.ResidueTrace
public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.ValuationRings.IntegralClosureAtOrdFiberNonneg
public import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegEqOneIsRational
public import Nyll.AlgebraicCurves.Places.Degree.FinrankPrimePow
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Trace.Quotient

/-!
# Place eval At trace eq sum fiber
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalAt_trace_eq_sum_fiber

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

open _root_.AlgebraicCurve _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place.ResidueTrace (algebraMap_evalAt_coe)
open _root_.AlgebraicCurve.Place.ResidueTrace.Assembly (residue_trace_eq_sum_evalAt)

/-- Integrality and evaluation of the trace at a rational place with rational fibre. -/
theorem _root_.AlgebraicCurve.Place.mem_and_evalAt_trace_eq_sum_fiber
    {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (f : F') (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) :
    Algebra.trace F F' f ∈ v.toValuationSubring ∧
      v.evalAt (Algebra.trace F F' f) = ∑ w ∈ v.fiber F', w.ramificationIndex F • w.evalAt f := by
  classical
  obtain ⟨c, rfl⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg (v := v) hf hord
  have htrace : Algebra.trace F F' (algebraMap (integralClosureAt F' v) F' c)
      = algebraMap v.toValuationSubring F
          (Algebra.trace v.toValuationSubring (integralClosureAt F' v) c) := by
    rw [← Algebra.algebraMap_intTrace (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v), Algebra.intTrace_eq_trace]
  refine ⟨by rw [htrace]; exact Subtype.coe_prop _, ?_⟩
  refine v.algebraMap_residueField_injective ?_
  rw [htrace, algebraMap_evalAt_coe v hv, residue_trace_eq_sum_evalAt hv hrat c, map_sum]
  exact Finset.sum_congr rfl fun w hw => (map_nsmul _ _ _).symm

/-- The residue trace for an element of order zero at every place in the fibre. -/
theorem _root_.AlgebraicCurve.Place.evalAt_trace_eq_sum_fiber {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (f : F') (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', w.ord f = 0) :
    v.evalAt (Algebra.trace F F' f) = ∑ w ∈ v.fiber F', w.ramificationIndex F • w.evalAt f :=
  (v.mem_and_evalAt_trace_eq_sum_fiber hv hrat f hf (fun w hw => (hord w hw).ge)).2

end
end AlgebraicCurves.Places.Proofs.Place_evalAt_trace_eq_sum_fiber
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
