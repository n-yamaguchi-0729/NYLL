/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistFiniteCohomology
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Vanishing of positive Čech cohomology for nonnegative twists

The existing coordinate contractions express every top-degree Laurent
monomial having a nonnegative exponent as a boundary. A monomial of
nonnegative total degree cannot have all exponents negative. Consequently
every top cochain is a boundary for a nonnegative twist. Together with the
existing contractions in intermediate degrees, this proves vanishing in
every positive cohomological degree over an arbitrary commutative ring.

The proof uses the actual monomial Čech complex and its existing
contractions. This is the free-module step of Serre vanishing, which is
needed when algebraizing coherent formal systems on projective schemes.
-/

noncomputable section

namespace ProjSpaceCech

universe u

open Finset
open AlgebraicCurves.Cohomology.Cech.Proofs
open ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist

/-- Nonnegative total degree ensures that at least one projective
coordinate has a nonnegative exponent. -/
theorem Twist.negSupp_ne_univ_of_sum_nonneg {n : ℕ} (a : Twist.MonExp n)
    (ha : 0 ≤ ∑ j, a j) : Twist.negSupp n a ≠ Finset.univ := by
  intro h
  have hneg : ∀ j : Fin (n + 1), a j < 0 := by
    intro j
    apply (Twist.mem_negSupp n).mp
    rw [h]
    exact Finset.mem_univ j
  have hsum : (∑ j : Fin (n + 1), a j) < ∑ _j : Fin (n + 1), (0 : ℤ) :=
    Finset.sum_lt_sum (fun j _ => (hneg j).le)
      ⟨0, Finset.mem_univ 0, hneg 0⟩
  rw [Finset.sum_const_zero] at hsum
  exact (not_lt_of_ge ha) hsum

/-- In top positive degree, each monomial of a nonnegative twist is a
boundary; finite sums give the assertion for the actual Čech quotient. -/
theorem Twist.subsingleton_cohomology_top_of_nonneg
    (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) (hd : 0 ≤ d) :
    Subsingleton (Twist.H R (m + 1) d (m + 1)) := by
  let L : Twist.Sec R (m + 1) d (Idx.img (m + 1) (sfull (m := m))) →ₗ[R]
      Twist.cochain R (m + 1) d (m + 1) :=
    LinearMap.single R
      (fun s : Idx (m + 1) (m + 1) => Twist.Sec R (m + 1) d (Idx.img (m + 1) s))
      (sfull (m := m))
  have hmem : ∀ v : Twist.Sec R (m + 1) d (Idx.img (m + 1) (sfull (m := m))),
      L v ∈ LinearMap.range (Twist.d R (m + 1) d m) := by
    intro v
    refine Finsupp.induction_linear v ?_ ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [map_add]
      exact Submodule.add_mem _ hv hw
    · intro b r
      have hb : Twist.negSupp (m + 1) b.val ≠ Finset.univ :=
        Twist.negSupp_ne_univ_of_sum_nonneg b.val (by rw [b.property.1]; exact hd)
      exact basis_mem_range R d b hb r
  change Subsingleton ((LinearMap.ker (Twist.d R (m + 1) d (m + 1))) ⧸
    (LinearMap.range (Twist.d R (m + 1) d m)).comap
      (LinearMap.ker (Twist.d R (m + 1) d (m + 1))).subtype)
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro f
  have hf : L (f.val (sfull (m := m))) = f.val := by
    funext s
    change Pi.single
      (M := fun t : Idx (m + 1) (m + 1) =>
        Twist.Sec R (m + 1) d (Idx.img (m + 1) t))
      (sfull (m := m)) (f.val (sfull (m := m))) s = f.val s
    rw [eq_sfull s, Pi.single_eq_same]
  change f.val ∈ LinearMap.range (Twist.d R (m + 1) d m)
  rw [← hf]
  exact hmem (f.val (sfull (m := m)))

/-- Nonnegative twists have no positive Čech cohomology, over any
commutative coefficient ring. -/
theorem Twist.subsingleton_cohomology_succ_of_nonneg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : 0 ≤ d) (i : ℕ) :
    Subsingleton (Twist.H R n d (i + 1)) := by
  rcases lt_trichotomy (i + 1) n with hlt | heq | hgt
  · exact subsingleton_cohomology_succ_of_le R d (Nat.succ_le_iff.mpr hlt)
  · subst n
    exact Twist.subsingleton_cohomology_top_of_nonneg R i d hd
  · exact subsingleton_cohomology_of_lt R n d hgt

end ProjSpaceCech
