/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusEvaluation
import Nyll.JacobianVarieties.Generalized.LocalUnitKernel
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolExistence

/-!
# The divisor-class boundary and local symbols

The principal boundary of a function which is a unit along the modulus
evaluates to the negative sum of its local symbols along that modulus.
For an isolated local jet this is precisely the negative of the single
local symbol. The boundary here is the existing actual divisor-class
boundary; no identification with a scheme kernel is postulated.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F A : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup A]
  [HasPrincipalDivisors K F] {D : Modulus K F} {a : Place K F → A}

/-- Evaluation of the actual principal kernel boundary is the finite
principal-divisor sum. -/
theorem HasModulus.classEvaluationZero_unitBoundary (ha : D.HasModulus a)
    (f : D.awayUnits) :
    ha.classEvaluationZero (D.unitBoundary (Additive.ofMul f)) =
      principalEvaluation a (Additive.ofMul f.1) := by
  change ha.classEvaluationZero (D.mkZero (D.unitDivisor f)) = _
  rw [ha.classEvaluationZero_mk, Divisor.evaluation_eq_finsum, principalEvaluation_apply]
  apply finsum_congr
  intro v
  rw [D.unitDivisor_apply]

/-- Reciprocity identifies kernel-boundary evaluation with the negative
sum of local symbols at the full modulus. -/
theorem HasModulus.classEvaluationZero_unitBoundary_eq_neg_sum (ha : D.HasModulus a)
    (f : D.awayUnits) :
    ha.classEvaluationZero (D.unitBoundary (Additive.ofMul f)) =
      -∑ v ∈ D.support, ha.localSymbol v (Additive.ofMul f.1) := by
  classical
  have hsupp : Function.support (fun v : Place K F =>
      ha.localSymbol v (Additive.ofMul f.1) - v.ord (f.1 : F) • a v) ⊆
        (D.support : Set (Place K F)) := by
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    intro hDv
    apply hv
    change ha.localSymbol v (Additive.ofMul f.1) - v.ord (f.1 : F) • a v = 0
    rw [ha.isLocalSymbol.2.1 v hDv f.1, sub_self]
  have hsum : (∑ᶠ v : Place K F,
      (ha.localSymbol v (Additive.ofMul f.1) - v.ord (f.1 : F) • a v)) =
        ∑ v ∈ D.support, ha.localSymbol v (Additive.ofMul f.1) := by
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    apply Finset.sum_congr rfl
    intro v hv
    rw [f.2 v (Finsupp.mem_support_iff.mp hv), zero_zsmul, sub_zero]
  rw [finsum_sub_distrib (ha.isLocalSymbol.finiteSupport f.1)
      (principalEvaluation_finiteSupport a f.1), ha.isLocalSymbol.2.2,
    zero_sub] at hsum
  rw [ha.classEvaluationZero_unitBoundary, principalEvaluation_apply]
  exact (neg_eq_iff_eq_neg).mp hsum

/-- For a jet supported at a single place, the boundary is minus the
local symbol, with the sign fixed by global reciprocity. -/
theorem HasModulus.classEvaluationZero_isolated_unitBoundary
    (ha : D.HasModulus a) (f : D.awayUnits) (v : Place K F) (hv : D v ≠ 0)
    (hisolated : ∀ w : Place K F, D w ≠ 0 → w ≠ v →
      w.CongruentOne (D w) (f.1 : F)) :
    ha.classEvaluationZero (D.unitBoundary (Additive.ofMul f)) =
      -ha.localSymbol v (Additive.ofMul f.1) := by
  classical
  rw [ha.classEvaluationZero_unitBoundary_eq_neg_sum]
  congr 1
  apply Finset.sum_eq_single v
  · intro w hw hwv
    exact ha.isLocalSymbol.1 w f.1 (hisolated w (Finsupp.mem_support_iff.mp hw) hwv)
  · intro hnot
    exact (hnot (Finsupp.mem_support_iff.mpr hv)).elim

end AlgebraicCurve.Modulus
