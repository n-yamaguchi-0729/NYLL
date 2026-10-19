/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Cohomology.CechRiemannRochGenusReached
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.EllAddEqOrd

/-!
# Exists forall subsingleton cech H1 nsmul of degree pos of riemann Genus Reached At
-/

section ProofImplementation

namespace AlgebraicCurve

theorem exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(riemannRochSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (hγ : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) (hD : 0 < Divisor.degree D) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Subsingleton (cechH1 S₀ S₁ ((n : ℤ) • D)) := by
  classical
  refine ⟨(Divisor.degree D₀ + γ).toNat, fun n hn => ?_⟩
  have : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := ‹FiniteDimensional K
    ↥(riemannRochSpace (0 : Divisor K F))›
  have RR := fun E : Divisor K F => cechRiemannRoch_of_genusReached hγ hcover h₀ h₁ E
  set E : Divisor K F := (n : ℤ) • D with hE
  set X : Divisor K F := E - D₀ with hX
  have hdegE : Divisor.degree E = (n : ℤ) * Divisor.degree D := by rw [hE, map_zsmul, smul_eq_mul]
  have hdegX : Divisor.degree X = (n : ℤ) * Divisor.degree D - Divisor.degree D₀ :=
    by rw [hX, map_sub, hdegE]
  have hn' : Divisor.degree D₀ + γ ≤ (n : ℤ) * Divisor.degree D := by
    have h1 : Divisor.degree D₀ + γ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((Divisor.degree D₀ + γ).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    nlinarith
  have hellX : 1 ≤ (ell X : ℤ) := by
    have := hγ.isMax X
    rw [hdegX] at this
    omega
  have hXne : ∃ h : F, h ∈ riemannRochSpace X ∧ h ≠ 0 := by
    by_contra hno
    push Not at hno
    have hbot : riemannRochSpace X = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro g hg; by_contra hg0; exact hg0 (hno g hg)
    have : ell X = 0 := by
      change Module.finrank K ↥(LSpace X) = 0
      rw [show LSpace X = riemannRochSpace X from rfl, hbot, finrank_bot]
    omega
  obtain ⟨h, hhX, hh0⟩ := hXne
  obtain ⟨P, hP, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) h hh0
  set E' : Divisor K F := E + P with hE'
  have hle : D₀ ≤ E' := by
    intro v
    have hv := (mem_riemannRochSpace_iff.mp hhX) v
    rcases hv with h0 | hv
    · exact absurd h0 hh0
    · rw [hE', Finsupp.add_apply, hP v]
      have : X v = E v - D₀ v := by rw [hX]; exact Finsupp.sub_apply _ _ _
      omega
  obtain ⟨-, hfinE, hh0E, hh1E, hχE, -⟩ := RR E
  obtain ⟨-, hfinE', hh0E', hh1E', hχE', hvanE'⟩ := RR E'
  have := hfinE
  have := hfinE'
  have hsub : Subsingleton (cechH1 S₀ S₁ E') := hvanE' hle
  have hi' : Module.finrank K (cechH1 S₀ S₁ E') = 0 := Module.finrank_zero_of_subsingleton
  have hellEE' : ell E' = ell E := ell_add_of_forall_eq_ord E hh0 hP
  have hdegE' : Divisor.degree E' = Divisor.degree E := by rw [hE', map_add, hPdeg, add_zero]
  have hiE : Module.finrank K (cechH1 S₀ S₁ E) = 0 := by
    have h1 := hχE; have h2 := hχE'
    rw [hh0E] at h1; rw [hh0E', hellEE', hdegE', hi'] at h2
    omega
  exact Module.finrank_zero_iff.mp hiE
end AlgebraicCurve
end ProofImplementation
