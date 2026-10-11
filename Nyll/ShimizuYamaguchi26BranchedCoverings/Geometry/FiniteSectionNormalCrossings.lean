/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.GeneralSectionIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Two crossing branches in a finite family of rational sections

At the point of the section `b` over `p`, the actual kernel ideal of a
section `c` becomes the unit ideal when `p` does not divide `Delta(c,b)`.
This follows from the previously computed actual intersection length.
Thus every other factor in a finite product of section ideals disappears
from the stalk, leaving the two branches whose determinant has valuation
one. Their previously constructed regular parameters prove strict normal
crossings for the entire finite product at this point.

This is the local two-branch implication needed in Lemma 2.3 of
Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The full finite-family criterion also needs the single-branch case, the
converse, and comparison with base change to `Z_p`. Identifying this product
with the reduced effective Cartier divisor of the paper is also a separate
construction.
-/

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

/-- A finite product of actual section ideals has strict normal crossings
at the point of `b` over `p` when exactly the selected two branches can meet
there and their determinant has valuation one. -/
theorem rationalSectionFamily_isStrictNormalCrossingsAt_of_two_branches
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (a b : Projectivization ℚ (ℚ × ℚ)) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hval : padicValInt p (rationalPointDelta a b) = 1)
    (hother : ∀ c ∈ A, c ≠ a → c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b) :
    (∏ c ∈ A, (rationalSection c).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p)) := by
  let x : ProjectiveLine ℤ := rationalSection b (integerPrimePoint p)
  have hstalk : (∏ c ∈ A, (rationalSection c).ker).stalkIdeal x =
      ((rationalSection a).ker * (rationalSection b).ker).stalkIdeal x := by
    rw [Scheme.IdealSheafData.stalkIdeal_finset_prod,
      Scheme.IdealSheafData.stalkIdeal_mul]
    apply Finset.prod_eq_mul_of_mem a b ha hb hab
    intro c hc hne
    have hunit : (rationalSection c).ker.stalkIdeal x = ⊤ :=
      rationalSection_stalkIdeal_eq_top_of_not_dvd p c b hne.2
        (hother c hc hne.1 hne.2)
    exact hunit.trans Ideal.one_eq_top.symm
  obtain ⟨hregular, d, r, t, hrpos, hrd, hparameters, hideal⟩ :=
    rationalSectionPair_isStrictNormalCrossingsAt p a b hab hval
  exact ⟨hregular, d, r, t, hrpos, hrd, hparameters, hstalk.trans hideal⟩

end ShimizuYamaguchi26BranchedCoverings
