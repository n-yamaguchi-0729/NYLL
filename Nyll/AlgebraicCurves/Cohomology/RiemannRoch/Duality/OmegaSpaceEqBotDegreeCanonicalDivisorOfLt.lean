/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_omegaSpace_eq_bot_of_degree_canonicalDivisorOf_lt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.FinrankOmegaSpaceEqEllCanonicalSub
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds

/-!
# Omega Space eq bot of degree canonical Divisor Of lt
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.OmegaSpaceBotDegreeCanonical
open AlgebraicCurve

theorem _root_.AlgebraicCurve.omegaSpace_eq_bot_of_degree_canonicalDivisorOf_lt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F] [Nonempty
      (AlgebraicCurve.Place K F)]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
      [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    {γ : ℤ} {D₀ : AlgebraicCurve.Divisor K F} (h : AlgebraicCurve.RiemannGenusReachedAt γ D₀)
    (hWK : AlgebraicCurve.WeilKaehlerAgree K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D :
      AlgebraicCurve.Divisor K F)
    [FiniteDimensional K ↥(AlgebraicCurve.omegaSpace (K := K) (F := F) D)]
    (hdeg : AlgebraicCurve.Divisor.degree (AlgebraicCurve.canonicalDivisorOf hω) <
      AlgebraicCurve.Divisor.degree D) :
    AlgebraicCurve.omegaSpace (K := K) (F := F) D = ⊥ := by
  have h1 := AlgebraicCurve.finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached h hWK hω D
  have h2 : AlgebraicCurve.ell (AlgebraicCurve.canonicalDivisorOf hω - D) = 0 :=
    AlgebraicCurve.ell_eq_zero_of_degree_neg (by rw [map_sub]; omega)
  rw [h2] at h1
  exact Submodule.finrank_eq_zero.mp h1
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.OmegaSpaceBotDegreeCanonical
end ProofImplementation
