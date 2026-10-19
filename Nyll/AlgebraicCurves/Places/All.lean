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

import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.ConstantExtension.All
import Nyll.AlgebraicCurves.Places.CountNormalizedFactorsSpanSingleton
import Nyll.AlgebraicCurves.Places.Degree.All
import Nyll.AlgebraicCurves.Places.Depth
import Nyll.AlgebraicCurves.Places.Differentials.All
import Nyll.AlgebraicCurves.Places.Evaluation.All
import Nyll.AlgebraicCurves.Places.GramDenominatorMulTable
import Nyll.AlgebraicCurves.Places.MemIffAdjoinSupLinearDisjoint
import Nyll.AlgebraicCurves.Places.NormTrace.All
import Nyll.AlgebraicCurves.Places.NotMemNeMem
import Nyll.AlgebraicCurves.Places.Orders.All
import Nyll.AlgebraicCurves.Places.Ramification.All
import Nyll.AlgebraicCurves.Places.Rational.All
import Nyll.AlgebraicCurves.Places.Residue.All
import Nyll.AlgebraicCurves.Places.Restriction.All
import Nyll.AlgebraicCurves.Places.SubfieldClosureRangeUnionEqTop
import Nyll.AlgebraicCurves.Places.Taylor.All
import Nyll.AlgebraicCurves.Places.UniqueMemIffAdjoinSupIsAlgebraic
import Nyll.AlgebraicCurves.Places.ValuationRings.All
