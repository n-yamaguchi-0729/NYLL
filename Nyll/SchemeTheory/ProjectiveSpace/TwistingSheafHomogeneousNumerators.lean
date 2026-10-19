/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Common homogeneous numerators for actual projective chart functions

Every regular function on a standard chart is represented by an actual
homogeneous numerator and a coordinate-power denominator. Finitely many
chart functions admit a common denominator exponent, as large as any
specified lower bound. The construction retains each numerator and the
exact equation in the native structure-sheaf sections.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization
open scoped BigOperators

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

private theorem coordinateFraction_mul_pow
    {A : Type*} [CommRing A] (f g p : A) (d k : ℕ) :
    Localization.mk (S := Submonoid.powers f) (p * g ^ k) ⟨f ^ (d + k), d + k, rfl⟩ =
      Localization.mk (S := Submonoid.powers f) p ⟨f ^ d, d, rfl⟩ *
        Localization.mk (S := Submonoid.powers f) g ⟨f ^ 1, 1, rfl⟩ ^ k := by
  rw [Localization.mk_pow, Localization.mk_mul]
  apply congrArg₂ (Localization.mk (S := Submonoid.powers f)) rfl
  apply Subtype.ext
  exact (pow_add f d k).trans (congrArg (f ^ d * ·) (congrArg (· ^ k) (pow_one f).symm))

/-- Multiplication by a coordinate power, with its actual homogeneous degree. -/
def homogeneousMulCoordinatePow (d : ℕ) (p : 𝒜 d) (j : Fin (n + 1)) (k : ℕ) :
    𝒜 (d + k) :=
  ⟨p.val * MvPolynomial.X j ^ k,
    p.property.mul (MvPolynomial.isHomogeneous_X_pow (R := R) j k)⟩

/-- Multiplying a homogeneous numerator by a coordinate power gives
the corresponding power of the regular coordinate ratio. -/
theorem homogeneousRatioSection_mulCoordinatePow (d : ℕ) (p : 𝒜 d)
    (i j : Fin (n + 1)) (k : ℕ) :
    homogeneousRatioSection R n (d + k) (homogeneousMulCoordinatePow R n d p j k) i =
      homogeneousRatioSection R n d p i * coordinateRatioSection R n i j ^ k := by
  unfold homogeneousRatioSection coordinateRatioSection
  rw [← map_pow, ← map_mul]
  apply congrArg (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, Away.val_mk,
    Away.val_mk]
  have h := coordinateFraction_mul_pow
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) (MvPolynomial.X j) p.val d k
  exact h

/-- Increasing a coordinate denominator while multiplying its numerator
by the missing power preserves the actual regular function. -/
theorem homogeneousRatioSection_eq_of_mul_coordinate_pow
    {d D : ℕ} (hdD : d ≤ D) (p : 𝒜 d) (q : 𝒜 D) (i : Fin (n + 1))
    (hq : q.val = p.val * MvPolynomial.X i ^ (D - d)) :
    homogeneousRatioSection R n D q i = homogeneousRatioSection R n d p i := by
  unfold homogeneousRatioSection
  apply congrArg (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  change MvPolynomial.X i ^ d * q.val = MvPolynomial.X i ^ D * p.val
  have hpow : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ^ d *
      MvPolynomial.X i ^ (D - d) = MvPolynomial.X i ^ D := by
    rw [← pow_add, Nat.add_sub_of_le hdD]
  calc
    MvPolynomial.X i ^ d * q.val =
        (MvPolynomial.X i ^ d * MvPolynomial.X i ^ (D - d)) * p.val := by
      rw [hq]
      ring
    _ = MvPolynomial.X i ^ D * p.val := by rw [hpow]

/-- An actual chart function has a homogeneous coordinate-fraction expression. -/
theorem exists_homogeneousRatioSection (i : Fin (n + 1))
    (s : Γ(Proj 𝒜, standardOpen R n i)) :
    ∃ d : ℕ, ∃ p : 𝒜 d, homogeneousRatioSection R n d p i = s := by
  let e := Proj.basicOpenIsoAway 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 s
  obtain ⟨d, p, hp, hpa⟩ := Away.mk_surjective 𝒜 (X_mem_one R n i) a
  have hp' : p ∈ 𝒜 d := by
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using hp
  refine ⟨d, ⟨p, hp'⟩, ?_⟩
  exact (congrArg e.hom hpa).trans ha

/-- A finite family of actual chart functions has homogeneous numerators
of one common degree, chosen above an arbitrary prescribed bound. -/
theorem exists_common_homogeneousRatioSection
    (s : ∀ i : Fin (n + 1), Γ(Proj 𝒜, standardOpen R n i)) (d : ℕ) :
    ∃ N : ℕ, d ≤ N ∧ ∃ p : Fin (n + 1) → 𝒜 N,
      ∀ i : Fin (n + 1), homogeneousRatioSection R n N (p i) i = s i := by
  classical
  choose m p hp using fun i => exists_homogeneousRatioSection R n i (s i)
  let N : ℕ := d + ∑ i : Fin (n + 1), m i
  have hm (i : Fin (n + 1)) : m i ≤ N :=
    (Finset.single_le_sum (f := m) (fun j _ => Nat.zero_le (m j))
      (Finset.mem_univ i)).trans (Nat.le_add_left _ d)
  let q (i : Fin (n + 1)) : 𝒜 N :=
    ⟨(p i).val * MvPolynomial.X i ^ (N - m i), by
      change ((p i).val * MvPolynomial.X i ^ (N - m i)).IsHomogeneous N
      have hq := (p i).property.mul (MvPolynomial.isHomogeneous_X_pow (R := R) i (N - m i))
      simpa only [Nat.add_sub_of_le (hm i)] using hq⟩
  refine ⟨N, Nat.le_add_right d _, q, fun i => ?_⟩
  exact (homogeneousRatioSection_eq_of_mul_coordinate_pow R n (hm i) (p i) (q i) i rfl).trans
    (hp i)

end AlgebraicGeometry.ProjSpace
