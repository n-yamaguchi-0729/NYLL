/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafLocalization
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Regular.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs

/-!
# Injective restriction between actual projective charts

Every coordinate ratio is a non-zero-divisor in the ring of its standard
chart. This is checked in the ordinary localization of the polynomial
ring, where both its numerator and denominator are coordinate variables.
Consequently restriction from a chart to any coordinate overlap is
injective over an arbitrary coefficient ring.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Multiplication by any coordinate ratio is injective on its standard
chart, even when the coefficient ring has zero-divisors. -/
theorem coordinateRatioSection_isLeftRegular (i j : Fin (n + 1)) :
    IsLeftRegular (coordinateRatioSection R n i j) := by
  have hM : ∀ m ∈ Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R),
      IsRegular m := by
    rintro m ⟨k, rfl⟩
    exact MvPolynomial.isRegular_X_pow (R := R) (n := i) k
  have hreg : IsRegular (ratio R n i j).val := by
    change IsRegular (Localization.mk (S := Submonoid.powers
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (MvPolynomial.X j)
      (⟨(MvPolynomial.X i) ^ 1, 1, rfl⟩ : Submonoid.powers (MvPolynomial.X i)))
    rw [Localization.mk_eq_mk']
    exact (IsLocalization.isRegular_mk'
      (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) hM).mpr
      (MvPolynomial.isRegular_X (R := R) (n := j))
  let e := Proj.basicOpenIsoAway 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
  intro a b hab
  obtain ⟨a', rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 a
  obtain ⟨b', rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 b
  apply congrArg e.hom
  apply HomogeneousLocalization.val_injective
  apply hreg.left
  have hab' : ratio R n i j * a' = ratio R n i j * b' := by
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    rw [map_mul, map_mul]
    exact hab
  have hv := congrArg HomogeneousLocalization.val hab'
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mul] at hv
  exact hv

/-- Restriction from a standard chart to its intersection with any other
standard chart is injective on actual regular functions. -/
theorem standardOpen_overlap_restrict_injective (i j : Fin (n + 1)) :
    Function.Injective
      (rO (inf_le_left : standardOpen R n i ⊓ standardOpen R n j ≤ standardOpen R n i)) := by
  let f : Γ(Proj 𝒜, standardOpen R n i) →+*
      Γ(Proj 𝒜, standardOpen R n i ⊓ standardOpen R n j) := rO inf_le_left
  let : Algebra Γ(Proj 𝒜, standardOpen R n i)
      Γ(Proj 𝒜, standardOpen R n i ⊓ standardOpen R n j) := f.toAlgebra
  have hU : IsAffineOpen (standardOpen R n i) :=
    Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
  have : IsLocalization.Away (coordinateRatioSection R n i j)
      Γ(Proj 𝒜, standardOpen R n i ⊓ standardOpen R n j) :=
    hU.isLocalization_of_eq_basicOpen (coordinateRatioSection R n i j)
      (homOfLE inf_le_left) (coordinateRatioSection_basicOpen R n i j).symm
  have hr : coordinateRatioSection R n i j ∈
      nonZeroDivisors Γ(Proj 𝒜, standardOpen R n i) := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro s hs
    exact coordinateRatioSection_isLeftRegular R n i j (hs.trans (mul_zero _).symm)
  exact IsLocalization.injective
    Γ(Proj 𝒜, standardOpen R n i ⊓ standardOpen R n j) (Submonoid.powers_le.mpr hr)

end AlgebraicGeometry.ProjSpace
