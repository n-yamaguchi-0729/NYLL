/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Mathlib.Algebra.BigOperators.Finprod

/-! # Additive evaluation of actual principal divisors

The principal-divisor theorem supplies finite support, so evaluation in an
arbitrary commutative group is an actual homomorphism on nonzero functions.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F A : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup A]
  [HasPrincipalDivisors K F]

/-- Principal-divisor evaluation has finite support for any values at places. -/
theorem principalEvaluation_finiteSupport (a : Place K F → A) (g : Fˣ) :
    Function.HasFiniteSupport (fun v => v.ord (g : F) • a v) := by
  classical
  obtain ⟨E, hE, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) (g : F) g.ne_zero
  refine E.support.finite_toSet.subset ?_
  intro v hv
  change v.ord (g : F) • a v ≠ 0 at hv
  apply Finsupp.mem_support_iff.mpr
  intro hEv
  apply hv
  rw [← hE v, hEv, zero_zsmul]

/-- Evaluation of a principal divisor in an arbitrary commutative group. -/
def principalEvaluation (a : Place K F → A) : Additive Fˣ →+ A where
  toFun g := ∑ᶠ v : Place K F, v.ord ((Additive.toMul g : Fˣ) : F) • a v
  map_zero' := by
    change (∑ᶠ v : Place K F, v.ord (1 : F) • a v) = 0
    simp only [Place.ord_one, zero_zsmul, finsum_zero]
  map_add' := by
    intro g h
    change (∑ᶠ v : Place K F,
      v.ord (((Additive.toMul g : Fˣ) : F) * ((Additive.toMul h : Fˣ) : F)) • a v) = _
    have heq (v : Place K F) :
        v.ord (((Additive.toMul g : Fˣ) : F) * ((Additive.toMul h : Fˣ) : F)) • a v =
          v.ord ((Additive.toMul g : Fˣ) : F) • a v +
            v.ord ((Additive.toMul h : Fˣ) : F) • a v := by
      rw [v.ord_mul (Additive.toMul g).ne_zero (Additive.toMul h).ne_zero, add_zsmul]
    simp_rw [heq]
    exact finsum_add_distrib (principalEvaluation_finiteSupport a (Additive.toMul g))
      (principalEvaluation_finiteSupport a (Additive.toMul h))

/-- The homomorphism is evaluated by the finite sum of the actual orders. -/
theorem principalEvaluation_apply (a : Place K F → A) (g : Fˣ) :
    principalEvaluation a (Additive.ofMul g) = ∑ᶠ v : Place K F, v.ord (g : F) • a v := rfl

end AlgebraicCurve
