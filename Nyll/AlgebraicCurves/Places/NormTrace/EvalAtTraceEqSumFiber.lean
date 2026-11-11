/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.lean
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

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace TraceValueProof
open _root_.AlgebraicCurve

export _root_.AlgebraicCurve.Place.ResidueTrace
  (trace_of_subsingleton
    trace_eq_smul_finrank_of_isNilpotent_sub_algebraMap
    ord_nonneg_of_mem
    mem_iff_ord_nonneg
    eq_ord_of_addHom_of_nonneg_iff
    residue_algebraMap
    algebraMap_evalAt_coe)

namespace Dict

export _root_.AlgebraicCurve.Place.ResidueTrace.Dict
  (neg_log_valuation_fiberCenter_eq_ord
    le_ord_iff_mem_pow_fiberCenter
    ramificationIndex_eq_ramificationIdx_fiberCenter
    toValuationSubringOfRestrictEq
    coe_toValuationSubringOfRestrictEq
    residueOfCenter
    residueOfCenter_apply
    ker_residueOfCenter
    surjective_residueOfCenter
    residueFieldEquivQuotientCenter
    residueFieldEquivQuotientCenter_mk
    placeCongrEquiv
    coe_placeCongrEquiv
    restrictResidueFieldEquiv
    restrictResidueFieldEquiv_residue
    inertiaDeg_eq_inertiaDeg_fiberCenter)

attribute [scoped simp] coe_toValuationSubringOfRestrictEq coe_placeCongrEquiv

end Dict

namespace Blocks

export _root_.AlgebraicCurve.Place.ResidueTrace.Blocks
  (instFreeIntegralClosureAt
    conductorIdeal
    conductorIdeal_ne_bot
    conductorQuotientAlgebra
    residue_trace_eq_trace_mk
    fiberCenterPow
    conductorIdeal_le_fiberCenterPow
    fiberCenterPowQuotientAlgebra
    instFiniteFiberCenterPowQuot
    instFreeFiberCenterPowQuot
    isNilpotent_mk_sub_algebraMap
    trace_mk_fiberCenterPow
    finrank_fiberCenterPow
    fiberIdeal
    fiberIdeal_of_mem
    fiberIdeal_of_notMem
    conductorIdeal_le_fiberIdeal
    isCoprime_fiberIdeal
    count_normalizedFactors_conductorIdeal
    conductorIdeal_eq_prod_fiber
    prod_fiberIdeal_le_of_subset
    conductorIdeal_le_prod_fiberIdeal
    fiberIdealQuotientAlgebra
    prodFiberIdealQuotientAlgebra
    finite_quotient_of_conductorLE
    trace_mk_prod_fiberIdeal
    trace_mk_conductor_eq_sum_fiber
    trace_mk_fiberIdeal_eq_trace_mk_fiberCenterPow)

attribute [scoped instance]
  instFreeIntegralClosureAt
  conductorQuotientAlgebra
  fiberCenterPowQuotientAlgebra
  instFiniteFiberCenterPowQuot
  instFreeFiberCenterPowQuot
  fiberIdealQuotientAlgebra
  prodFiberIdealQuotientAlgebra

end Blocks

namespace Assembly

export _root_.AlgebraicCurve.Place.ResidueTrace.Assembly
  (sub_algebraMap_evalAt_mem_fiberCenter
    residue_trace_eq_sum_evalAt)

end Assembly

end AlgebraicCurve.TraceValueProof

open _root_.AlgebraicCurves.Places.Proofs in
open _root_.AlgebraicCurve.Place hiding
  mem_iff_ord_nonneg
  ord_nonneg_of_mem
  le_ord_iff_mem_pow_fiberCenter
  neg_log_valuation_fiberCenter_eq_ord
  eq_ord_of_addHom_of_nonneg_iff in
open _root_.AlgebraicCurve in
open Place_evalAt_trace_eq_sum_fiber.AlgebraicCurve in
open TraceValueProof in
open TraceValueProof.Assembly in
theorem _root_.AlgebraicCurve.Place.evalAt_trace_eq_sum_fiber {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (f : F') (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', w.ord f = 0) :
    v.evalAt (Algebra.trace F F' f) = ∑ w ∈ v.fiber F', w.ramificationIndex F • w.evalAt f := by
  classical
  obtain ⟨c, rfl⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg
    (v := v) hf (fun w hw => (hord w hw).ge)
  have htrace : Algebra.trace F F' (algebraMap (integralClosureAt F' v) F' c)
      = algebraMap v.toValuationSubring F
          (Algebra.trace v.toValuationSubring (integralClosureAt F' v) c) := by
    rw [← Algebra.algebraMap_intTrace (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v), Algebra.intTrace_eq_trace]
  refine v.algebraMap_residueField_injective ?_
  rw [htrace, algebraMap_evalAt_coe v hv, residue_trace_eq_sum_evalAt hv hrat c, map_sum]
  exact Finset.sum_congr rfl fun w hw => (map_nsmul _ _ _).symm

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
