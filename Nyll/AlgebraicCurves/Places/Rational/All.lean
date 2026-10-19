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

import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.Differentials
import Nyll.AlgebraicCurves.Places.Rational.FiniteOrder
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Nyll.AlgebraicCurves.Places.Rational.RatFuncRationalPlaceIntegralBase
import Nyll.AlgebraicCurves.Places.Rational.RatFuncSquareFibers
import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegEqOneAlgClosed
import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegNeZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegreeEqZeroEqOrd
import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegreeEqZeroEqOrdAlgebraMap
import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegreeEqZeroPrincipal
import Nyll.AlgebraicCurves.Places.Rational.RatFuncEllSubEllEqGenusZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncEqPlaceInftyIffNeOfHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Rational.RatFuncEvalAtPlaceInftyEq
import Nyll.AlgebraicCurves.Places.Rational.RatFuncEvalAtPlaceOfPointAlgebraMap
import Nyll.AlgebraicCurves.Places.Rational.RatFuncAlgEquivCongrRingEquivPlaceInftyEqPlaceOfPointZeroEq
import Nyll.AlgebraicCurves.Places.Rational.RatFuncAlgebraMapOrdEqZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncNeOfHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Rational.RatFuncFiniteDimensionalLSpaceZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncFiniteSetOfOrdNeZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncHasPrincipalDivisors
import Nyll.AlgebraicCurves.Places.Rational.RatFuncIndexOfSpecialtyFinite
import Nyll.AlgebraicCurves.Places.Rational.RatFuncPrincipalDegreeEqZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncMapDomainEqOrdDivMap
import Nyll.AlgebraicCurves.Places.Rational.RatFuncPlaceRatFuncTower
import Nyll.AlgebraicCurves.Places.Rational.RatFuncOrdXSubC
import Nyll.AlgebraicCurves.Places.Rational.RatFuncOrdPlaceInftyEqOrdPlaceInftyAddSumOrdPlaceOfPoint
import Nyll.AlgebraicCurves.Places.Rational.RatFuncStichtenothGenusExists
import Nyll.AlgebraicCurves.Places.Rational.RatFuncStichtenothGenusExistsRatFuncTower
import Nyll.AlgebraicCurves.Places.Rational.RatFuncSubsingletonSetOfNeOfHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Rational.RatFuncToValuationSubringEq
import Nyll.AlgebraicCurves.Places.Rational.RatFuncGlobalResidueFormula
import Nyll.AlgebraicCurves.Places.Rational.RatFuncTraceLocalResidueFinitePlaceDivPowEqZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncTraceLocalResiduePlaceInftyXPowEqZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncWeilReciprocity
