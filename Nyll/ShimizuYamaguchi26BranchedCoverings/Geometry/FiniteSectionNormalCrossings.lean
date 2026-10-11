/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.GeneralSectionIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Closure
import Mathlib.Topology.Maps.Basic

/-!
# Normal crossings in a finite family of rational sections

At the point of the section `b` over `p`, the actual kernel ideal of a
section `c` becomes the unit ideal when `p` does not divide `Delta(c,b)`.
This follows from the previously computed actual intersection length.
Thus every other factor in a finite product of section ideals disappears
from the stalk. A single remaining branch is a regular parameter; two
remaining branches whose determinant has valuation one form the previously
constructed regular parameter system. In either case the entire finite
product has strict normal crossings at this point. The determinant filter
selects these cases directly when its cardinality is at most two. The actual
support of the product and the section identity then give the same result
at every support point lying over `p`.

These are the local one- and two-branch implications needed in Lemma 2.3 of
Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The full finite-family criterion still needs the converse and comparison
with base change to `Z_p`. Identifying this product
with the reduced effective Cartier divisor of the paper is also a separate
construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

/-- A finite product of actual section ideals has strict normal crossings
at the point of `b` over `p` when every other section is disjoint there. -/
theorem rationalSectionFamily_isStrictNormalCrossingsAt_of_one_branch
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A)
    (hother : ∀ c ∈ A, c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b) :
    (∏ c ∈ A, (rationalSection c).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p)) := by
  let x : ProjectiveLine ℤ := rationalSection b (integerPrimePoint p)
  have hstalk : (∏ c ∈ A, (rationalSection c).ker).stalkIdeal x =
      (rationalSection b).ker.stalkIdeal x := by
    rw [Scheme.IdealSheafData.stalkIdeal_finset_prod]
    apply Finset.prod_eq_single_of_mem b hb
    intro c hc hne
    have hunit : (rationalSection c).ker.stalkIdeal x = ⊤ :=
      rationalSection_stalkIdeal_eq_top_of_not_dvd p c b hne (hother c hc hne)
    exact hunit.trans Ideal.one_eq_top.symm
  obtain ⟨hregular, d, r, t, hrpos, hrd, hparameters, hideal⟩ :=
    rationalSection_isStrictNormalCrossingsAt p b
  exact ⟨hregular, d, r, t, hrpos, hrd, hparameters, hstalk.trans hideal⟩

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

/-- The determinant incidence count and valuation-one condition imply
strict normal crossings at the actual point of a selected section.
The selected section itself belongs to the count because its self-determinant is zero. -/
theorem rationalSectionFamily_isStrictNormalCrossingsAt_of_card_le_two
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A)
    (hcard : (A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b)).card ≤ 2)
    (hval : ∀ a ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
      padicValInt p (rationalPointDelta a b) = 1) :
    (∏ c ∈ A, (rationalSection c).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p)) := by
  classical
  let S : Finset (Projectivization ℚ (ℚ × ℚ)) :=
    A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b)
  have hbS : b ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    rw [rationalPointDelta_self]
    exact dvd_zero (p : ℤ)
  by_cases hsecond : ∃ a ∈ S, a ≠ b
  · obtain ⟨a, haS, hab⟩ := hsecond
    have ha : a ∈ A := (Finset.mem_filter.mp haS).1
    have hpab : (p : ℤ) ∣ rationalPointDelta a b := (Finset.mem_filter.mp haS).2
    have hpair : ({a, b} : Finset (Projectivization ℚ (ℚ × ℚ))) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact haS
        · exact hbS
      · rw [Finset.card_pair hab]
        exact hcard
    apply rationalSectionFamily_isStrictNormalCrossingsAt_of_two_branches
      p A a b ha hb hab (hval a ha hab hpab)
    intro c hc hca hcb hpdiv
    have hcS : c ∈ S := Finset.mem_filter.mpr ⟨hc, hpdiv⟩
    rw [← hpair] at hcS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcS
    exact hcS.elim hca hcb
  · apply rationalSectionFamily_isStrictNormalCrossingsAt_of_one_branch p A b hb
    intro c hc hcb hpdiv
    exact hsecond ⟨c, Finset.mem_filter.mpr ⟨hc, hpdiv⟩, hcb⟩

/-- The arithmetic incidence-count conditions give strict normal crossings
at every support point over the selected prime. The supporting section is
obtained from the actual ideal-sheaf product, and its base point is recovered
from the section identity. -/
theorem rationalSectionFamily_isStrictNormalCrossingsAt_over_prime
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (hcard : ∀ b ∈ A,
      (A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b)).card ≤ 2)
    (hval : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
      padicValInt p (rationalPointDelta a b) = 1)
    (x : ProjectiveLine ℤ) (hx : x ∈ (∏ c ∈ A, (rationalSection c).ker).support)
    (hbase : ProjSpace.π ℤ 1 x = integerPrimePoint p) :
    (∏ c ∈ A, (rationalSection c).ker).IsStrictNormalCrossingsAt x := by
  classical
  have hsupport : ∀ B : Finset (Projectivization ℚ (ℚ × ℚ)),
      x ∈ (∏ c ∈ B, (rationalSection c).ker).support →
        ∃ b ∈ B, x ∈ (rationalSection b).ker.support := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
        intro hxB
        rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
          Scheme.IdealSheafData.support_top] at hxB
        exact False.elim hxB
    | @insert a B ha ih =>
        intro hxB
        rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul] at hxB
        change x ∈ (rationalSection a).ker.support ∨
          x ∈ (∏ c ∈ B, (rationalSection c).ker).support at hxB
        rcases hxB with hxa | hxB
        · exact ⟨a, Finset.mem_insert_self a B, hxa⟩
        · obtain ⟨b, hb, hxb⟩ := ih hxB
          exact ⟨b, Finset.mem_insert_of_mem hb, hxb⟩
  obtain ⟨b, hb, hxb⟩ := hsupport A hx
  rw [Scheme.Hom.support_ker,
    (rationalSection b).isClosedEmbedding.isClosed_range.closure_eq] at hxb
  obtain ⟨q, hqx⟩ := hxb
  have hq : q = integerPrimePoint p := by
    calc
      q = (rationalSection b ≫ ProjSpace.π ℤ 1) q := by
        rw [rationalSection_comp_π]
      _ = ProjSpace.π ℤ 1 x := by rw [Scheme.Hom.comp_apply, hqx]
      _ = integerPrimePoint p := hbase
  have hbx : rationalSection b (integerPrimePoint p) = x := hq ▸ hqx
  rw [← hbx]
  exact rationalSectionFamily_isStrictNormalCrossingsAt_of_card_le_two
    p A b hb (hcard b hb) (fun a ha hab hpab => hval a ha b hb hab hpab)

end ShimizuYamaguchi26BranchedCoverings
