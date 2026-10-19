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

import Nyll.AlgebraicCurves.Hilbert.Functor.All
import Nyll.AlgebraicCurves.Hilbert.PointIEqSpanFinrankPieceSuccLe
import Nyll.AlgebraicCurves.Hilbert.PointFlatCompIdealBasicOpenEqSpan
import Nyll.AlgebraicCurves.Hilbert.CoverFinrankPieceEqClosedImmersionFlatNoetherian
import Nyll.AlgebraicCurves.Hilbert.CoverFinrankPieceEqClosedImmersionFlatFinitePresentation
import Nyll.AlgebraicCurves.Hilbert.FinrankPieceEqEvalClosedImmersion
import Nyll.AlgebraicCurves.Hilbert.FibreH0RankTensorPowEqHilbertFunctionOf
import Nyll.AlgebraicCurves.Hilbert.IdealMemIffAppAwayToSectionEqZeroPolynomial
import Nyll.AlgebraicCurves.Hilbert.IdealProjectivePieceSuccIff
import Nyll.AlgebraicCurves.Hilbert.ClosedImmersionFinitePresentationFactorsIffMem
import Nyll.AlgebraicCurves.Hilbert.LinearEquivBaseChangePieceMap
import Nyll.AlgebraicCurves.Hilbert.PointIEqMap
import Nyll.AlgebraicCurves.Hilbert.PointIEqSpanSurjective
import Nyll.AlgebraicCurves.Hilbert.PointMemIffClosedImmersion
import Nyll.AlgebraicCurves.Hilbert.PointHilbertFunctionOfMemIff
import Nyll.AlgebraicCurves.Hilbert.UniformCoverGeomFibreIdealEqPoint
import Nyll.AlgebraicCurves.Hilbert.FreePieceLocalRing
import Nyll.AlgebraicCurves.Hilbert.MapMemIffTmulMkQPieceEqZero
import Nyll.AlgebraicCurves.Hilbert.MemXPowMulMem
import Nyll.AlgebraicCurves.Hilbert.SymmetricPowerData
