/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafLocalization
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Actual compatible numerators for a projective local section

Quasicoherent localization first extends a given section separately
across every standard affine chart after multiplying by a coordinate
power. The finitely many exponents are replaced by their sum. On each
pairwise overlap the difference of the two resulting numerators
vanishes after restriction to the original chart. The kernel clause
of localization kills this difference by another coordinate power.
Taking one common power for all overlaps gives compatible numerators.

Every numerator is an actual section of the original module sheaf.
The compatibility and the exponents are conclusions of the construction.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules Scheme.Modules.GlueOfCocycle

private abbrev res {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens}
    (h : W ≤ V) : Γ(F, V) →+ Γ(F, W) :=
  (F.presheaf.map (homOfLE h).op).hom

private theorem res_res {X : Scheme.{u}} (F : X.Modules)
    {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(F, U)) :
    res F hWV (res F hVU s) = res F (hWV.trans hVU) s := by
  change (F.presheaf.map (homOfLE hVU).op ≫ F.presheaf.map (homOfLE hWV).op) s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private theorem res_smul {X : Scheme.{u}} (F : X.Modules)
    {V W : X.Opens} (h : W ≤ V) (r : Γ(X, V)) (s : Γ(F, V)) :
    res F h (r • s) = rO h r • res F h s :=
  F.map_smul (homOfLE h) r s

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- One exponent gives actual numerators on all standard affine charts. -/
theorem exists_uniform_coordinate_numerators (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F]
    (i : Fin (n + 1)) (s : Γ(F, standardOpen R n i)) :
    ∃ d : ℕ, ∃ t : ∀ j : Fin (n + 1), Γ(F, standardOpen R n j), ∀ j,
      F.presheaf.map
          (homOfLE (inf_le_left : standardOpen R n j ⊓ standardOpen R n i ≤
            standardOpen R n j)).op (t j) =
        (rO (inf_le_left : standardOpen R n j ⊓ standardOpen R n i ≤
          standardOpen R n j) (coordinateRatioSection R n j i)) ^ d •
          F.presheaf.map (homOfLE (inf_le_right : standardOpen R n j ⊓
            standardOpen R n i ≤ standardOpen R n i)).op s := by
  classical
  have hlocal : ∀ j : Fin (n + 1), ∃ (d : ℕ) (t : Γ(F, standardOpen R n j)),
      res F (inf_le_left : standardOpen R n j ⊓ standardOpen R n i ≤
          standardOpen R n j) t =
        (rO (inf_le_left : standardOpen R n j ⊓ standardOpen R n i ≤
          standardOpen R n j) (coordinateRatioSection R n j i)) ^ d •
          res F inf_le_right s := by
    intro j
    have hchart : IsAffineOpen (standardOpen R n j) :=
      Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j) (X_mem_one R n j) one_pos
    obtain ⟨d, t, ht⟩ := (coordinateRatioSection_localization R n F j i hchart le_rfl).1
      (res F inf_le_right s)
    exact ⟨d, t, by simpa only [rO_refl, map_pow] using ht⟩
  choose d t ht using hlocal
  let e : ℕ := ∑ j : Fin (n + 1), d j
  refine ⟨e, fun j => (coordinateRatioSection R n j i) ^ (e - d j) • t j, ?_⟩
  intro j
  have hj : d j ≤ e :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (d k)) (Finset.mem_univ j)
  change res F inf_le_left ((coordinateRatioSection R n j i) ^ (e - d j) • t j) = _
  rw [res_smul, map_pow, ht j, smul_smul, ← pow_add, Nat.sub_add_cancel hj]

/-- Coordinate powers can be chosen so that all actual numerators satisfy
the transition relation on every pairwise overlap. -/
theorem exists_compatible_coordinate_numerators (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F]
    (i : Fin (n + 1)) (s : Γ(F, standardOpen R n i)) :
    ∃ d : ℕ, ∃ t : ∀ j : Fin (n + 1), Γ(F, standardOpen R n j),
      (∀ j, F.presheaf.map
          (homOfLE (inf_le_left : standardOpen R n j ⊓ standardOpen R n i ≤
            standardOpen R n j)).op (t j) =
        (rO (inf_le_left : standardOpen R n j ⊓ standardOpen R n i ≤
          standardOpen R n j) (coordinateRatioSection R n j i)) ^ d •
          F.presheaf.map (homOfLE (inf_le_right : standardOpen R n j ⊓
            standardOpen R n i ≤ standardOpen R n i)).op s) ∧
      (∀ j k, F.presheaf.map
          (homOfLE (inf_le_left : standardOpen R n j ⊓ standardOpen R n k ≤
            standardOpen R n j)).op (t j) =
        (rO (inf_le_left : standardOpen R n j ⊓ standardOpen R n k ≤
          standardOpen R n j) (coordinateRatioSection R n j k)) ^ d •
          F.presheaf.map (homOfLE (inf_le_right : standardOpen R n j ⊓
            standardOpen R n k ≤ standardOpen R n k)).op (t k)) := by
  classical
  obtain ⟨d, t, ht⟩ := exists_uniform_coordinate_numerators R n F i s
  have hkernel : ∀ j k : Fin (n + 1), ∃ e : ℕ,
      (rO (inf_le_left : standardOpen R n j ⊓ standardOpen R n k ≤
        standardOpen R n j) (coordinateRatioSection R n j i)) ^ e •
      (res F (inf_le_left : standardOpen R n j ⊓ standardOpen R n k ≤
          standardOpen R n j) (t j) -
        (rO (inf_le_left : standardOpen R n j ⊓ standardOpen R n k ≤
          standardOpen R n j) (coordinateRatioSection R n j k)) ^ d •
          res F (inf_le_right : standardOpen R n j ⊓ standardOpen R n k ≤
            standardOpen R n k) (t k)) = 0 := by
    intro j k
    let V : (Proj 𝒜).Opens := standardOpen R n j ⊓ standardOpen R n k
    let b : Γ(Proj 𝒜, V) := rO inf_le_left (coordinateRatioSection R n j k)
    let δ : Γ(F, V) := res F inf_le_left (t j) - b ^ d • res F inf_le_right (t k)
    have hWj : V ⊓ standardOpen R n i ≤ standardOpen R n j :=
      inf_le_left.trans inf_le_left
    have hWk : V ⊓ standardOpen R n i ≤ standardOpen R n k :=
      inf_le_left.trans inf_le_right
    have ej : res F hWj (t j) =
        (rO hWj (coordinateRatioSection R n j i)) ^ d • res F inf_le_right s := by
      have h := congrArg (res F (le_inf hWj inf_le_right)) (ht j)
      simpa only [res_res, res_smul, map_pow, rO_rO] using h
    have ek : res F hWk (t k) =
        (rO hWk (coordinateRatioSection R n k i)) ^ d • res F inf_le_right s := by
      have h := congrArg (res F (le_inf hWk inf_le_right)) (ht k)
      simpa only [res_res, res_smul, map_pow, rO_rO] using h
    have hzero : res F (inf_le_left : V ⊓ standardOpen R n i ≤ V) δ = 0 := by
      change res F inf_le_left (res F inf_le_left (t j) -
        (rO inf_le_left (coordinateRatioSection R n j k)) ^ d •
          res F inf_le_right (t k)) = 0
      rw [map_sub, res_smul, res_res, res_res, map_pow, rO_rO, ej, ek,
        smul_smul, ← mul_pow, coordinateRatioSection_mul R n j k i hWj hWk, sub_self]
    have hV : IsAffineOpen V := by
      change IsAffineOpen (standardOpen R n j ⊓ standardOpen R n k)
      rw [← coordinateRatioSection_basicOpen]
      exact (Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j)
        (X_mem_one R n j) one_pos).basicOpen (coordinateRatioSection R n j k)
    exact (coordinateRatioSection_localization R n F j i hV inf_le_left).2 δ hzero
  choose e he using hkernel
  let E : ℕ := ∑ j : Fin (n + 1), ∑ k : Fin (n + 1), e j k
  refine ⟨E + d, fun j => (coordinateRatioSection R n j i) ^ E • t j, ?_, ?_⟩
  · intro j
    change res F inf_le_left ((coordinateRatioSection R n j i) ^ E • t j) = _
    rw [res_smul, map_pow, ht j, smul_smul, ← pow_add]
  · intro j k
    let V : (Proj 𝒜).Opens := standardOpen R n j ⊓ standardOpen R n k
    let a : Γ(Proj 𝒜, V) := rO inf_le_left (coordinateRatioSection R n j i)
    let b : Γ(Proj 𝒜, V) := rO inf_le_left (coordinateRatioSection R n j k)
    let c : Γ(Proj 𝒜, V) := rO inf_le_right (coordinateRatioSection R n k i)
    let δ : Γ(F, V) := res F inf_le_left (t j) - b ^ d • res F inf_le_right (t k)
    have hinner : e j k ≤ ∑ l : Fin (n + 1), e j l :=
      Finset.single_le_sum (fun l _ => Nat.zero_le (e j l)) (Finset.mem_univ k)
    have houter : (∑ l : Fin (n + 1), e j l) ≤ E :=
      Finset.single_le_sum (fun l _ => Nat.zero_le (∑ q : Fin (n + 1), e l q))
        (Finset.mem_univ j)
    have hejk : a ^ (e j k) • δ = 0 := he j k
    have hkill : a ^ E • δ = 0 := by
      calc
        a ^ E • δ = a ^ (E - e j k) • (a ^ (e j k) • δ) := by
          rw [smul_smul, ← pow_add, Nat.sub_add_cancel (hinner.trans houter)]
        _ = 0 := by rw [hejk, smul_zero]
    have habc : b * c = a :=
      coordinateRatioSection_mul R n j k i inf_le_left inf_le_right
    have hcoef : a ^ E * b ^ d = b ^ (E + d) * c ^ E := by
      rw [← habc, mul_pow, pow_add]
      ring
    have heq : a ^ E • res F (W := V) inf_le_left (t j) =
        a ^ E • (b ^ d • res F (W := V) inf_le_right (t k)) := by
      apply sub_eq_zero.mp
      exact (smul_sub (a ^ E) (res F (W := V) inf_le_left (t j))
        (b ^ d • res F (W := V) inf_le_right (t k))).symm.trans hkill
    change res F (W := V) inf_le_left ((coordinateRatioSection R n j i) ^ E • t j) =
      b ^ (E + d) • res F (W := V) inf_le_right
        ((coordinateRatioSection R n k i) ^ E • t k)
    rw [res_smul, res_smul, map_pow, map_pow]
    change a ^ E • res F (W := V) inf_le_left (t j) =
      b ^ (E + d) • (c ^ E • res F (W := V) inf_le_right (t k))
    rw [heq, smul_smul, smul_smul, hcoef]

end AlgebraicGeometry.ProjSpace
