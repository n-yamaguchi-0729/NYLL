/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Differentials.Residues.Canonical
import Nyll.AlgebraicCurves.Differentials.Residues.Construction
import Nyll.AlgebraicCurves.Differentials.Residues.UniqueHasSimpleResidue
import Nyll.AlgebraicCurves.Differentials.Residues.LinearMapHasSimpleResidueKerEqRegularRangeEqSumZeroFinrankCorner
import Nyll.AlgebraicCurves.Differentials.Residues.MemPolarDifferentialsHasSimpleResidue
import Nyll.AlgebraicCurves.Differentials.Residues.PlaceResidueEqAlgebraMap
import Nyll.AlgebraicCurves.Differentials.Residues.PlaceRingHomResidueEqIsPrimeLe
import Nyll.AlgebraicCurves.Differentials.Residues.FibreIdentity
import Nyll.AlgebraicCurves.Differentials.Residues.FibreResidueIdentityAlong
import Nyll.AlgebraicCurves.Differentials.Residues.HasCanonicalLocalResidueK
import Nyll.AlgebraicCurves.Differentials.Residues.KaehlerResidueTermDiagonalHomEqZero
import Nyll.AlgebraicCurves.Differentials.Residues.RationalSimplePoles
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremKAlgClosed
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremKRatFunc
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremFunctionField
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremAlgClosed
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremPerfectField
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremResidueTheoremK
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremResidueTheoremRatFunc
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremRatFuncPerfectField
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTraceCompletionCommute
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueNormEqNormResidue
import Nyll.AlgebraicCurves.Differentials.Residues.SumEqZeroHasSimpleResidue
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTraceProjection
import Nyll.AlgebraicCurves.Differentials.Residues.TateAgreement
import Nyll.AlgebraicCurves.Differentials.Residues.TateChainRule
import Nyll.AlgebraicCurves.Differentials.Residues.TateCommFinite
import Nyll.AlgebraicCurves.Differentials.Residues.TateTrace
import Nyll.AlgebraicCurves.Differentials.Residues.TateTraceCompatSeparable
import Nyll.AlgebraicCurves.Differentials.Residues.WeilKaehlerAgreeResidueTheorem
