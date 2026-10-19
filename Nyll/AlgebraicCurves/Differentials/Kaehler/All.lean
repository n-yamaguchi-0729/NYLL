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

import Nyll.AlgebraicCurves.Differentials.Kaehler.AlgebraTraceInvMulDerivationEqInvNormMulDerivationNorm
import Nyll.AlgebraicCurves.Differentials.Kaehler.DerivationAddMulLeftPowChar
import Nyll.AlgebraicCurves.Differentials.Kaehler.FunctionField
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialDNeZero
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialMapInjective
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialSpanDEqTop
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialUniqueSmulD
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerRankOneTranscendental
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerToFunctionFieldEqSmulDCoord
import Nyll.AlgebraicCurves.Differentials.Kaehler.TranscendentalSeparable
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Differentials.Kaehler.WeilDifferentialRankOne
import Nyll.AlgebraicCurves.Differentials.Kaehler.WeilOfKaehlerNeZeroMaximal
