/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Prime.Defs
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Ring

/-!
# The reduced ideal of a primitive section equation

The infinity-chart equation of primitive integral coordinates `(u,v)` is
`v-u*w`. When `u` is nonzero, coprimality makes this polynomial irreducible,
and unique factorization in `ℤ[w]` makes its principal ideal prime. When
`u` is zero, `v` is a unit and the ideal is the unit ideal.

Thus the equation ideal is radical in both cases. This is the algebraic
step needed to pass from the closed support of the actual integral section
to its scheme-theoretic equation ideal in Lemma 2.3 of Shimizu and Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

/-- The principal ideal of the section equation in the integral infinity chart. -/
def infinitySectionIdeal (u v : ℤ) : Ideal ℤ[X] :=
  Ideal.span {Polynomial.C v - Polynomial.C u * Polynomial.X}

/-- A primitive nonconstant section equation generates a prime ideal. -/
theorem infinitySectionIdeal_isPrime (u v : ℤ) (hu : u ≠ 0)
    (huv : IsCoprime u v) : (infinitySectionIdeal u v).IsPrime := by
  have hirr : Irreducible (Polynomial.C (-u) * Polynomial.X + Polynomial.C v) :=
    Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr hu) huv.isRelPrime.neg_left
  have heq : Polynomial.C (-u) * Polynomial.X + Polynomial.C v =
      Polynomial.C v - Polynomial.C u * Polynomial.X := by
    rw [map_neg]
    ring
  rw [heq] at hirr
  exact Ideal.isPrime_span_singleton_of_prime hirr.prime

/-- The section equation ideal is reduced for every primitive coordinate pair. -/
theorem infinitySectionIdeal_isRadical (u v : ℤ) (huv : IsCoprime u v) :
    (infinitySectionIdeal u v).IsRadical := by
  by_cases hu : u = 0
  · subst u
    have hv : IsUnit v := isCoprime_zero_left.mp huv
    have htop : infinitySectionIdeal 0 v = ⊤ := by
      simp only [infinitySectionIdeal, map_zero, zero_mul, sub_zero]
      exact Ideal.span_singleton_eq_top.mpr (hv.map Polynomial.C)
    rw [htop]
    change (⊤ : Ideal ℤ[X]).radical ≤ ⊤
    exact le_top
  · exact (infinitySectionIdeal_isPrime u v hu huv).isRadical

/-- The vanishing ideal of the primitive equation's zero locus is the equation ideal itself. -/
theorem vanishingIdeal_infinitySectionIdeal (u v : ℤ) (huv : IsCoprime u v) :
    PrimeSpectrum.vanishingIdeal
        (PrimeSpectrum.zeroLocus (infinitySectionIdeal u v : Set ℤ[X])) =
      infinitySectionIdeal u v := by
  rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (infinitySectionIdeal_isRadical u v huv).radical

end ShimizuYamaguchi26BranchedCoverings
