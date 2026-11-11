/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.ValuationRings.BasicValuationSubring
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.ValuedFieldTheory.Valuation.Subring.Integral.IntegralCriterion

/-!
# Is Integral adjoin of forall ord nonneg
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.IsIntegral_adjoin_of_forall_ord_nonneg

open AlgebraicCurve Polynomial

namespace INTGlue

theorem isIntegral_of_mem_adjoin_inv {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    {z : F} (hz0 : z ≠ 0) (hmem : z ∈ Algebra.adjoin A ({z⁻¹} : Set F)) : IsIntegral A z :=
  _root_.Algebra.isIntegral_of_mem_adjoin_inv hz0 hmem

theorem isIntegral_of_forall_valuationSubring {F : Type*} [Field F] (A : Subring F) (z : F)
    (h : ∀ V : ValuationSubring F, A ≤ V.toSubring → z ∈ V) : IsIntegral A z :=
  _root_.Subring.isIntegral_of_mem_all_valuationSubrings A z h

end INTGlue

theorem _root_.AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg {K F : Type*} [Field K] [Field
  F] [Algebra K F] [CharZero K] (t : F)
    (_ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    [AlgebraicCurve.HasPrincipalDivisors K F] (z : F)
    (hz : ∀ v : AlgebraicCurve.Place K F, 0 ≤ v.ord t → 0 ≤ v.ord z) :
    IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by
  classical
  have key : IsIntegral (Algebra.adjoin K ({t} : Set F)).toSubring z := by
    refine INTGlue.isIntegral_of_forall_valuationSubring _ z fun V hV => ?_
    by_cases hz0 : z = 0
    · rw [hz0]; exact V.zero_mem
    by_cases htop : V = ⊤
    · rw [htop]; exact ValuationSubring.mem_top z
    have hK : ∀ a : K, algebraMap K F a ∈ V := fun a =>
      hV (Subalgebra.algebraMap_mem (Algebra.adjoin K ({t} : Set F)) a)
    obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_of_valuationSubring t V hK htop
    have htV : t ∈ v.toValuationSubring := by
      rw [hv]; exact hV (Algebra.subset_adjoin (Set.mem_singleton t))
    have h1 : 0 ≤ v.ord t := v.ord_nonneg_of_mem htV
    have h2 := AlgebraicCurve.Place.mem_of_ord_nonneg v hz0 (hz v h1)
    rwa [hv] at h2
  exact key
end AlgebraicCurves.Places.Proofs.IsIntegral_adjoin_of_forall_ord_nonneg
end ProofImplementation
