/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_residueTheorem_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Differentials.Residues.TateTrace
import Nyll.AlgebraicCurves.Differentials.Residues.Construction
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremRatFuncPerfectField
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremResidueTheoremRatFunc
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTraceCompletionCommute

/-!
# Residue Theorem of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_perfectField

open AlgebraicCurve

theorem _root_.AlgebraicCurve.residueTheorem_of_perfectField
    {K F : Type*} [Field K] [PerfectField K]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [Algebra.IsSeparable (RatFunc K) F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheorem K F := by
  classical
  exact AlgebraicCurve.residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
      (AlgebraicCurve.residueTheorem_ratFunc_of_perfectField K)
      (AlgebraicCurve.residueTraceCompletionCommute (K := K) (F := F) (E := RatFunc K))
end AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheorem_of_perfectField
end ProofImplementation
