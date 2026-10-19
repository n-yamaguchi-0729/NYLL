/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.FunctionFields.LinearAlgebra.LinearIndependentPowTranscendental
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.DegreeCanonicalDivisorEq
import Nyll.AlgebraicCurves.Places.Rational.RatFuncFiniteDimensionalLSpaceZero

import Nyll.AlgebraicCurves.Places.Basic

/-!
# Genus eq zero of is Principal single sub single
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusZeroPrincipalSingleSub
namespace AlgebraicCurve
open _root_.AlgebraicCurve

theorem genus_eq_zero_of_degree_one_principal_difference {K : Type*} {F : Type*} [Field K]
  [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {P Q : Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genus K F = 0 := by
  classical
  obtain ⟨f, hf0, hdiv⟩ := h
  have hordQ : Q.ord f = -1 := by
    have := hdiv Q
    rw [Finsupp.sub_apply, Finsupp.single_apply, ite_eq_right hPQ, Finsupp.single_eq_same] at this
    linarith [this]
  have hordv : ∀ v : Place K F, v ≠ Q → 0 ≤ v.ord f := by
    intro v hv
    have := hdiv v
    rw [← this, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, ite_eq_right
      (Ne.symm hv)]
    by_cases hvP : P = v
    · rw [ite_eq_left hvP]; norm_num
    · rw [ite_eq_right hvP]; norm_num
  have : Nonempty (Place K F) := ⟨Q⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  have : Nontrivial Ω[F⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2
  have hftr : Transcendental K f := by
    intro halg
    have hint : IsIntegral K f := halg.isIntegral
    have hmem : f ∈ Q.toValuationSubring := by
      have hint' : IsIntegral Q.toValuationSubring f := hint.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Q.toValuationSubring) (K :=
        F)).mp hint'
      rw [← hy]; exact y.2
    have := Q.ord_nonneg_of_mem hmem
    linarith
  have hpow : ∀ n k : ℕ, k ≤ n → f ^ k ∈ LSpace ((n : ℤ) • Finsupp.single Q (1 : ℤ)) := by
    intro n k hk
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    rw [← zpow_natCast, Place.ord_zpow]
    by_cases hv : v = Q
    · subst hv
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, hordQ]
      omega
    · have h0 : ((n : ℤ) • Finsupp.single Q (1 : ℤ)) v = 0 := by
        rw [Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hv), smul_zero]
      rw [h0, neg_zero]
      exact mul_nonneg (by positivity) (hordv v hv)
  have hell : ∀ n : ℕ, (n : ℤ) + 1 ≤ (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) := by
    intro n
    set D : Divisor K F := (n : ℤ) • Finsupp.single Q (1 : ℤ)
    have : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
    let g : Fin (n + 1) → LSpace D := fun k => ⟨f ^ (k : ℕ), hpow n k (Nat.lt_succ_iff.mp k.2)⟩
    have hli : LinearIndependent K g := by
      have h1 : LinearIndependent K (fun k : Fin (n + 1) => f ^ (k : ℕ)) :=
        (linearIndependent_pow_of_transcendental hftr).comp (fun k : Fin (n+1) => (k : ℕ))
          (fun a b hab => Fin.ext hab)
      exact LinearIndependent.of_comp (LSpace D).subtype (by exact h1)
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    change (n : ℤ) + 1 ≤ (Module.finrank K (LSpace D) : ℤ)
    exact_mod_cast this
  obtain ⟨ω, hω⟩ : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  have hdegK := degree_canonicalDivisor_eq_of_riemannRoch hRR hC hω
  have hdegD : Divisor.degree (((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ)) = ((2 * genus
    K F : ℕ) : ℤ) := by
    rw [map_zsmul, Divisor.degree_single, hQ, Nat.cast_one, mul_one, zsmul_eq_mul, mul_one]
    exact Int.cast_natCast _
  have hRRD := hRR hω (((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ))
  have hzero : ell (canonicalDivisorOf hω - ((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ))
    = 0 := by
    apply ell_eq_zero_of_degree_neg
    rw [map_sub, hdegK, hdegD]; push_cast; omega
  rw [hzero, hdegD] at hRRD
  have hlow := hell (2 * genus K F)
  push_cast at hlow hRRD ⊢
  omega

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs in
open _root_.AlgebraicCurve in
open GenusZeroPrincipalSingleSub.AlgebraicCurve in
theorem _root_.AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single {K : Type*} {F :
  Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {P Q : Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genus K F = 0 :=
  AlgebraicCurve.genus_eq_zero_of_degree_one_principal_difference hRR hC hPQ hQ h
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusZeroPrincipalSingleSub
end ProofImplementation
