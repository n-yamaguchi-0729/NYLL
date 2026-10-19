/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Ring

/-!
# The actual coordinate transition functions for the twisting sheaf

The regular function `X j / X i` on the standard chart `D₊(X i)` is
obtained from the homogeneous localization through the structure sheaf
map. Its multiplicative identity on intersections is proved in the
localization at each projective point. These functions therefore give
an actual unit cocycle, with no transition identity assumed as data.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard projective chart on which the specified coordinate is nonzero. -/
abbrev standardOpen (i : Fin (n + 1)) : (Proj 𝒜).Opens :=
  Proj.basicOpen 𝒜 (MvPolynomial.X i)

/-- A homogeneous coordinate ratio as an actual regular section. -/
def coordinateRatioSection (i j : Fin (n + 1)) : Γ(Proj 𝒜, standardOpen R n i) :=
  Proj.awayToSection 𝒜 (MvPolynomial.X i) (ratio R n i j)

theorem coordinateRatioSection_self (i : Fin (n + 1)) :
    coordinateRatioSection R n i i = 1 := by
  exact (congrArg (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom
    (ratio_self R n i)).trans (map_one (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom)

/-- Multiplication of coordinate ratios on every common subopen. -/
theorem coordinateRatioSection_mul (i j k : Fin (n + 1))
    {V : (Proj 𝒜).Opens} (hi : V ≤ standardOpen R n i)
    (hj : V ≤ standardOpen R n j) :
    rO hi (coordinateRatioSection R n i j) *
        rO hj (coordinateRatioSection R n j k) =
      rO hi (coordinateRatioSection R n i k) := by
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
      (ratio R n i j) *
    HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj)
      (ratio R n j k)).val =
    (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxi)
      (ratio R n i k)).val
  rw [HomogeneousLocalization.val_mul]
  change Localization.mk (MvPolynomial.X j)
      ⟨(MvPolynomial.X i) ^ 1, pow_mem hxi 1⟩ *
    Localization.mk (MvPolynomial.X k)
      ⟨(MvPolynomial.X j) ^ 1, pow_mem hxj 1⟩ =
    Localization.mk (MvPolynomial.X k)
      ⟨(MvPolynomial.X i) ^ 1, pow_mem hxi 1⟩
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, pow_one, one_mul]
  ring

/-- The standard projective cover, with its index in the scheme's universe. -/
abbrev twistingCover (i : ULift.{u} (Fin (n + 1))) : (Proj 𝒜).Opens :=
  standardOpen R n i.down

theorem iSup_twistingCover : ⨆ i, twistingCover R n i = ⊤ := by
  apply top_unique
  rw [← Proj.iSup_basicOpen_eq_top 𝒜
    (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (irrelevant_le_span_X R n)]
  apply iSup_le
  intro i
  exact le_iSup (twistingCover R n) (ULift.up i)

/-- The transition cocycle for `𝒪(1)`, whose entry is `X j / X i`. -/
def twistingCocycle : UnitCocycle (twistingCover R n) where
  u i j := rO inf_le_left (coordinateRatioSection R n i.down j.down)
  refl i := by rw [coordinateRatioSection_self, map_one]
  cocycle i j k := by
    rw [rO_rO, rO_rO, rO_rO]
    exact coordinateRatioSection_mul R n i.down j.down k.down _ _

end AlgebraicGeometry.ProjSpace
