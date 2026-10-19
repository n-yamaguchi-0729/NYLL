/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_weilSmul_eq_of_riemannIndexFormula.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.WeilDifferentialRankOne
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.RingNF

/-! The Riemann index formula makes any two nonzero Weil differentials proportional. -/

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsWeilSmulRiemannIndex

noncomputable section

open _root_.AlgebraicCurve Module
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs.WeilDifferentialRankOne
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs
open IndexOfSpecialty_eq_of_genusReached.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_add_one_sub_genus_le_ell_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) (D : Divisor K F) :
    Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ) := by
  have hi := hRI D
  have hi0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

theorem omegaSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ)) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by
  have h0 : 0 < finrank K (adeleSpace K F ⧸ adeleBddPrincipal K F D) := by
    rw [← indexOfSpecialty_eq]
    have hi := hRI D
    have h0' : (0 : ℤ) < (indexOfSpecialty D : ℤ) := by linarith
    exact_mod_cast h0'
  have : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=
    FiniteDimensional.of_finrank_pos h0
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

theorem lSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < Divisor.degree D + 1 - (genus K F : ℤ)) :
    Module.Finite K (LSpace (K := K) (F := F) D) := by
  have h0 : (0 : ℤ) < (ell D : ℤ) :=
    lt_of_lt_of_le hpos (degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI D)
  exact FiniteDimensional.of_finrank_pos (by exact_mod_cast h0)

theorem _root_.AlgebraicCurve.exists_weilSmul_eq_of_riemannIndexFormula {K : Type*} {F : Type*}
  [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * genus K F + 2 * (Divisor.degree W).natAbs + 4 with hn
  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
  have hg0 : (0 : ℤ) ≤ (genus K F : ℤ) := Int.natCast_nonneg _
  have habs0 : (0 : ℤ) ≤ |Divisor.degree W| := abs_nonneg _
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W := neg_abs_le _
  have habsW' : Divisor.degree W ≤ |Divisor.degree W| := le_abs_self _
  have hn_ge : 3 * (genus K F : ℤ) + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by
    nlinarith [Int.natCast_nonneg n]
  have hndegP_pos : 0 < (n : ℤ) * (P.deg : ℤ) := by nlinarith
  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; linarith)
  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + (genus K F : ℤ) := by
    have h := hRI D
    rw [hellD, hdegD] at h; push_cast at h; linarith
  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - (genus K F : ℤ)
      ≤ (ell (W - D) : ℤ) := by
    have h := degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI (W - D)
    rw [hdegWD] at h; exact h
  have hiDpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ) := by
    rw [hellD, hdegD]; push_cast; nlinarith
  have hellWDpos : 0 < Divisor.degree (W - D) + 1 - (genus K F : ℤ) := by
    rw [hdegWD]; nlinarith
  have := omegaSpace_finite_of_riemannIndexFormula hRI hiDpos
  have := lSpace_finite_of_riemannIndexFormula hRI hellWDpos
  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon
  rw [hiD] at hdbl
  nlinarith

end

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsWeilSmulRiemannIndex
