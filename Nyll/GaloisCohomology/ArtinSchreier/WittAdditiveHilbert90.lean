/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Tactic.Ring

/-!
# Additive Hilbert 90 at every finite Witt length

A field trace-one element has a Teichmüller lift whose Witt trace has
constant coefficient one, hence is a unit. Dividing by this invariant unit
gives actual Witt trace one. The usual finite sum then kills every additive
Witt cocycle, including in the wild case.
-/

@[expose] public section

noncomputable section

namespace ArtinSchreierWittTheory

variable (p : ℕ) [Fact p.Prime] {K Ω : Type*} [Field K] [Field Ω]
  [CharP Ω p] [Algebra K Ω] [IsGalois K Ω] [FiniteDimensional K Ω]

/-- A finite Galois field extension has a Witt vector of Galois trace one. -/
theorem exists_witt_galois_sum_eq_one :
    ∃ w : WittVector p Ω, ∑ σ : Gal(Ω/K), WittVector.map σ.toRingHom w = 1 := by
  classical
  obtain ⟨a, ha⟩ := Algebra.trace_surjective K Ω 1
  have htrace : ∑ σ : Gal(Ω/K), σ a = 1 := by
    rw [← trace_eq_sum_automorphisms, ha, map_one]
  let s : WittVector p Ω :=
    ∑ σ : Gal(Ω/K), WittVector.map σ.toRingHom (WittVector.teichmuller p a)
  have hs0 : s.coeff 0 = 1 := by
    change WittVector.constantCoeff s = 1
    rw [map_sum]
    change (∑ σ : Gal(Ω/K), σ a) = 1
    exact htrace
  have hsfix (σ : Gal(Ω/K)) : WittVector.map σ.toRingHom s = s := by
    rw [map_sum]
    have hcomp (τ : Gal(Ω/K)) :
        WittVector.map σ.toRingHom (WittVector.map τ.toRingHom (WittVector.teichmuller p a)) =
          WittVector.map (σ * τ).toRingHom (WittVector.teichmuller p a) := by
      apply WittVector.ext
      exact fun _ => rfl
    simp only [hcomp]
    exact Fintype.sum_bijective (fun τ : Gal(Ω/K) => σ * τ)
      (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)
  obtain ⟨u, hu⟩ := WittVector.isUnit_of_coeff_zero_ne_zero s (hs0.trans_ne one_ne_zero)
  let v : WittVector p Ω := ↑u⁻¹
  have hsv : s * v = 1 := u.mul_inv_of_eq hu
  have hvs : v * s = 1 := u.inv_mul_of_eq hu
  have hvfix (σ : Gal(Ω/K)) : WittVector.map σ.toRingHom v = v := by
    have hσ := congrArg (WittVector.map σ.toRingHom) hsv
    rw [map_mul, hsfix, map_one] at hσ
    calc
      WittVector.map σ.toRingHom v = (v * s) * WittVector.map σ.toRingHom v := by
        rw [hvs, one_mul]
      _ = v * (s * WittVector.map σ.toRingHom v) := mul_assoc _ _ _
      _ = v := by rw [hσ, mul_one]
  refine ⟨WittVector.teichmuller p a * v, ?_⟩
  calc
    (∑ σ : Gal(Ω/K), WittVector.map σ.toRingHom (WittVector.teichmuller p a * v)) =
        ∑ σ : Gal(Ω/K), WittVector.map σ.toRingHom (WittVector.teichmuller p a) * v := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [map_mul, hvfix]
    _ = s * v := (Finset.sum_mul _ _ _).symm
    _ = 1 := hsv

/-- Every additive cocycle with values in a finite Witt ring is a coboundary. -/
theorem additiveHilbert90_finite (m : ℕ) (c : Gal(Ω/K) → TruncatedWittVector p m Ω)
    (hc : ∀ σ τ : Gal(Ω/K), c (σ * τ) =
      TruncatedWittVector.map σ.toRingHom (c τ) + c σ) :
    ∃ β : TruncatedWittVector p m Ω, ∀ σ : Gal(Ω/K),
      TruncatedWittVector.map σ.toRingHom β - β = c σ := by
  classical
  obtain ⟨w, hw⟩ := exists_witt_galois_sum_eq_one p (K := K) (Ω := Ω)
  let t : TruncatedWittVector p m Ω := WittVector.truncate m w
  have ht : (∑ τ : Gal(Ω/K), TruncatedWittVector.map τ.toRingHom t) = 1 := by
    have h := congrArg (WittVector.truncate m) hw
    rw [map_sum, map_one] at h
    simpa only [t, TruncatedWittVector.map_wittVector_truncate] using h
  let B : TruncatedWittVector p m Ω :=
    ∑ τ : Gal(Ω/K), c τ * TruncatedWittVector.map τ.toRingHom t
  have hB (σ : Gal(Ω/K)) : TruncatedWittVector.map σ.toRingHom B = B - c σ := by
    have hperm : (∑ τ : Gal(Ω/K), c (σ * τ) * TruncatedWittVector.map (σ * τ).toRingHom t) = B :=
      Fintype.sum_bijective (fun τ : Gal(Ω/K) => σ * τ)
        (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)
    have hpermTrace : (∑ τ : Gal(Ω/K), TruncatedWittVector.map (σ * τ).toRingHom t) = 1 := by
      rw [Fintype.sum_bijective (fun τ : Gal(Ω/K) => σ * τ)
        (Group.mulLeft_bijective σ) _ (fun τ => TruncatedWittVector.map τ.toRingHom t)
        (fun _ => rfl)]
      exact ht
    have hcomp (τ : Gal(Ω/K)) :
        TruncatedWittVector.map σ.toRingHom (TruncatedWittVector.map τ.toRingHom t) =
          TruncatedWittVector.map (σ * τ).toRingHom t := by
      apply TruncatedWittVector.ext
      intro i
      simp only [TruncatedWittVector.map_coeff]
      rfl
    calc
      TruncatedWittVector.map σ.toRingHom B =
          ∑ τ : Gal(Ω/K), (c (σ * τ) - c σ) * TruncatedWittVector.map (σ * τ).toRingHom t := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro τ _
        rw [map_mul, hc, add_sub_cancel_right, hcomp]
      _ = (∑ τ : Gal(Ω/K), c (σ * τ) * TruncatedWittVector.map (σ * τ).toRingHom t) -
          c σ * (∑ τ : Gal(Ω/K), TruncatedWittVector.map (σ * τ).toRingHom t) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = B - c σ := by rw [hperm, hpermTrace, mul_one]
  refine ⟨-B, ?_⟩
  intro σ
  rw [map_neg, hB]
  ring

end ArtinSchreierWittTheory
