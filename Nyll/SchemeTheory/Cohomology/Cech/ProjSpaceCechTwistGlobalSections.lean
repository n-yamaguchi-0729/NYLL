/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistFiniteCohomology
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistPositiveVanishing
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic.SplitIfs

/-!
# Global sections of nonnegative projective twists

The canonical map sends each homogeneous monomial with nonnegative
exponents to the same Laurent monomial on every coordinate chart. The
actual Čech cocycle equations force all chart coefficients to agree.
If a Laurent monomial has a negative exponent, nonnegative total degree
provides a coordinate outside its negative support, where its coefficient
must vanish. Thus the canonical map is bijective, including in projective
dimension zero.

The resulting equivalence retains the explicit map to chart sections.
It supplies the polynomial-numerator calculation needed to lift global
sections through finite graded presentations.
-/

noncomputable section

namespace ProjSpaceCech.Twist

universe u

open AlgebraicCurves.Cohomology.Cech.Proofs
open ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist

variable (R : Type u) [CommRing R] {n : ℕ} (d : ℤ)

/-- The canonical homogeneous-monomial map to actual degree-zero Čech
cohomology. -/
def constSectionMap : (Mon n d ∅ →₀ R) →ₗ[R] H R n d 0 :=
  (constSec R d).codRestrict (LinearMap.ker (Twist.d R n d 0))
    (constSec_mem_ker R d)

/-- The map to global sections retains each monomial coefficient, as
can be read on any one coordinate chart. -/
theorem constSectionMap_injective : Function.Injective (constSectionMap R (n := n) d) := by
  intro x y hxy
  have hcochain : constSec R d x = constSec R d y := congrArg Subtype.val hxy
  have hchart := congrFun hcochain (vtx (0 : Fin (n + 1)))
  change Finsupp.mapDomain (Mon.incl n d (Finset.empty_subset _)) x =
    Finsupp.mapDomain (Mon.incl n d (Finset.empty_subset _)) y at hchart
  exact Finsupp.mapDomain_injective (Mon.incl_injective n d _) hchart

private theorem coeff_eq_zero_of_negSupp_ne_empty
    (hd : 0 ≤ d) (f : cochain R n d 0)
    (hf : f ∈ LinearMap.ker (Twist.d R n d 0)) (s : Idx n 0)
    (a : MonExp n) (ha : ∑ j, a j = d) (hne : negSupp n a ≠ ∅) :
    coeff R d f s a = 0 := by
  have hproper : negSupp n a ≠ Finset.univ :=
    negSupp_ne_univ_of_sum_nonneg a (by rw [ha]; exact hd)
  have hnotall : ¬ ∀ j : Fin (n + 1), j ∈ negSupp n a :=
    fun hall => hproper (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨k, hk⟩ := Classical.not_forall.mp hnotall
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [eq_vtx s, ker_edge R d hf (s.val 0) k]
  apply coeff_of_not R d f (vtx k) a
  rw [img_vtx]
  intro hsubset
  exact hk ((Finset.mem_singleton.mp (hsubset hj)) ▸ hj)

/-- In a nonnegative twist, every actual global section has a homogeneous
polynomial numerator. This also covers projective dimension zero. -/
theorem constSectionMap_surjective (hd : 0 ≤ d) :
    Function.Surjective (constSectionMap R (n := n) d) := by
  intro f
  refine ⟨Finsupp.comapDomain (Mon.incl n d (Finset.empty_subset _))
    (f.val (vtx (0 : Fin (n + 1))))
    (Set.injOn_of_injective (Mon.incl_injective n d _)), ?_⟩
  apply Subtype.ext
  apply ext_coeff R d
  intro s a
  change coeff R d (constSec R d _) s a = coeff R d f.val s a
  rw [coeff_constSec]
  split_ifs with ha
  · erw [Finsupp.comapDomain_apply,
      show Mon.incl n d (Finset.empty_subset _) ⟨a, ha.1, ha.2.le⟩ =
        (⟨a, ha.1, ha.2.le.trans (Finset.empty_subset _)⟩ :
          Mon n d (Idx.img n (vtx (0 : Fin (n + 1))))) from rfl,
      ← coeff_eq R d f.val (vtx (0 : Fin (n + 1))),
      eq_vtx s, ker_edge R d f.property]
  · by_cases hdeg : ∑ j, a j = d
    · exact (coeff_eq_zero_of_negSupp_ne_empty R d hd f.val f.property s a hdeg
        (fun hzero => ha ⟨hdeg, hzero⟩)).symm
    · rw [coeff, dite_eq_right (fun h => hdeg h.1)]

/-- Explicit homogeneous monomial coordinates on the global sections
of a nonnegative projective twist. -/
def globalSectionsEquiv (hd : 0 ≤ d) : (Mon n d ∅ →₀ R) ≃ₗ[R] H R n d 0 :=
  LinearEquiv.ofBijective (constSectionMap R d)
    ⟨constSectionMap_injective R d, constSectionMap_surjective R d hd⟩

end ProjSpaceCech.Twist
