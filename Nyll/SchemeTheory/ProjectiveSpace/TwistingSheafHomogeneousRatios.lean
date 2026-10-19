/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Ring

/-!
# Actual homogeneous polynomial ratios on projective charts

The homogeneous polynomial `p` of degree `d` gives the actual regular
function `p / X i ^ d` on the `i`-th standard chart. Its chart map is
injective over an arbitrary coefficient ring, because each coordinate
variable is regular. The change-of-chart equation is proved in the
localization at each projective point.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The actual regular function represented by a homogeneous polynomial
divided by the matching power of a coordinate. -/
def homogeneousRatioSection (d : ℕ) (p : 𝒜 d) (i : Fin (n + 1)) :
    Γ(Proj 𝒜, standardOpen R n i) :=
  Proj.awayToSection 𝒜 (MvPolynomial.X i)
    (Away.mk 𝒜 (X_mem_one R n i) d p.val (by
      simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using p.property))

theorem homogeneousRatioSection_zero (d : ℕ) (i : Fin (n + 1)) :
    homogeneousRatioSection R n d 0 i = 0 := by
  have h : Away.mk 𝒜 (X_mem_one R n i) d 0 (by
      simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using (𝒜 d).zero_mem) = 0 := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]
  exact (congrArg (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom h).trans
    (map_zero (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom)

theorem homogeneousRatioSection_add (d : ℕ) (p q : 𝒜 d) (i : Fin (n + 1)) :
    homogeneousRatioSection R n d (p + q) i =
      homogeneousRatioSection R n d p i + homogeneousRatioSection R n d q i := by
  unfold homogeneousRatioSection
  rw [← map_add]
  apply congrArg (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
    Localization.add_mk_self]
  rfl

/-- The homogeneous chart map retains addition. -/
def homogeneousRatioSectionAddHom (d : ℕ) (i : Fin (n + 1)) :
    𝒜 d →+ Γ(Proj 𝒜, standardOpen R n i) where
  toFun p := homogeneousRatioSection R n d p i
  map_zero' := homogeneousRatioSection_zero R n d i
  map_add' p q := homogeneousRatioSection_add R n d p q i

/-- Changing the coordinate denominator gives precisely the transition
function of the `d`-th tensor power of the twisting sheaf. -/
theorem homogeneousRatioSection_transition (d : ℕ) (p : 𝒜 d) (i j : Fin (n + 1))
    {V : (Proj 𝒜).Opens} (hi : V ≤ standardOpen R n i)
    (hj : V ≤ standardOpen R n j) :
    rO hi (homogeneousRatioSection R n d p i) =
      rO hi (coordinateRatioSection R n i j) ^ d *
        rO hj (homogeneousRatioSection R n d p j) := by
  apply Subtype.ext
  funext x
  have : x.val.asHomogeneousIdeal.toIdeal.IsPrime :=
    (show ProjectiveSpectrum 𝒜 from x.val).isPrime
  have hxi : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∈
      x.val.asHomogeneousIdeal.toIdeal.primeCompl := hi x.property
  have hxj : (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈
      x.val.asHomogeneousIdeal.toIdeal.primeCompl := hj x.property
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxi)
      (Away.mk 𝒜 (X_mem_one R n i) d p.val _)).val =
    ((HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxi)
      (ratio R n i j)) ^ d *
      HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj)
        (Away.mk 𝒜 (X_mem_one R n j) d p.val _)).val
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  change Localization.mk p.val ⟨(MvPolynomial.X i) ^ d, pow_mem hxi d⟩ =
    (Localization.mk (MvPolynomial.X j)
      ⟨(MvPolynomial.X i) ^ 1, pow_mem hxi 1⟩) ^ d *
    Localization.mk p.val ⟨(MvPolynomial.X j) ^ d, pow_mem hxj d⟩
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    pow_one, one_mul]
  ring

/-- A homogeneous polynomial is determined by its regular function on
any single standard chart. No integral-domain assumption is needed. -/
theorem homogeneousRatioSection_injective (d : ℕ) (i : Fin (n + 1)) :
    Function.Injective (fun p : 𝒜 d => homogeneousRatioSection R n d p i) := by
  intro p q hpq
  let e := Proj.basicOpenIsoAway 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
  have hm : Away.mk 𝒜 (X_mem_one R n i) d p.val (by
      simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using p.property) =
    Away.mk 𝒜 (X_mem_one R n i) d q.val (by
      simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using q.property) :=
    (ConcreteCategory.bijective_of_isIso e.hom).1 hpq
  have hv := congrArg HomogeneousLocalization.val hm
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists] at hv
  obtain ⟨a, ha⟩ := hv
  obtain ⟨k, hk⟩ := a.property
  change (a.val : MvPolynomial (Fin (n + 1)) R) * ((MvPolynomial.X i) ^ d * p.val) =
    a.val * ((MvPolynomial.X i) ^ d * q.val) at ha
  rw [← hk] at ha
  apply Subtype.ext
  exact (MvPolynomial.isRegular_X_pow (R := R) (n := i) d).left
    ((MvPolynomial.isRegular_X_pow (R := R) (n := i) k).left ha)

end AlgebraicGeometry.ProjSpace
