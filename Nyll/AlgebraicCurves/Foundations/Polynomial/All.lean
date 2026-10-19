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

import Nyll.AlgebraicCurves.Foundations.Polynomial.MacaulayMonomials
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialEvalNeZeroMacaulayPowFinrankPieceSupAddLe
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialEvalNeZeroMemMulMemFinrankPieceSupEqMacaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialEvalNeZeroMemMulMem
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialSumCMulXMulMemImp
import Nyll.AlgebraicCurves.Foundations.Polynomial.MacaulayMonomialSubspace
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceAddTwoEqMacaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceEq
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceSuccLeMacaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceSupSpanSingletonSuccAddFinrankPieceEq
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceSuccEqMacaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialLeFinrankPiece
import Nyll.AlgebraicCurves.Foundations.Polynomial.RingHomLaurentSeriesDerivativeEq
