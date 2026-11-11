/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.StalkDimension
public import Nyll.SchemeTheory.Etale.GeometricFiberSplitSection
public import Nyll.SchemeTheory.Etale.Neighborhoods
public import Nyll.SchemeTheory.Etale.HenselianLocalGeometricLift
public import Nyll.SchemeTheory.Etale.AffineClosedLift
public import Nyll.SchemeTheory.Etale.AffineResidueField
public import Nyll.SchemeTheory.Etale.AffineGeometricFiberBound
public import Nyll.SchemeTheory.Etale.AffineFinitePresentationRefinement
public import Nyll.SchemeTheory.Etale.AffineLocalFactorDescent
public import Nyll.SchemeTheory.Etale.ChosenResidueExtension
public import Nyll.SchemeTheory.Etale.ClosedNeighborhoodEqualizer
public import Nyll.SchemeTheory.Etale.ClosedNeighborhoodLift
public import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
public import Nyll.SchemeTheory.Etale.FiniteStrictLocalSection
public import Nyll.SchemeTheory.Etale.FiniteAffineCover
public import Nyll.SchemeTheory.Etale.FiniteRadicialLocalSection
public import Nyll.SchemeTheory.Etale.GeometricFiberNeighborhood
public import Nyll.SchemeTheory.Etale.IsomorphismNeighborhood
public import Nyll.SchemeTheory.Etale.NormalizationRemainder
public import Nyll.SchemeTheory.Etale.NormalizationRemainderDegree
public import Nyll.SchemeTheory.Etale.OverField.All
public import Nyll.SchemeTheory.Etale.ProperLocalCover
public import Nyll.SchemeTheory.Etale.ResidueBaseChange
public import Nyll.SchemeTheory.Etale.ResidueFieldExtension
public import Nyll.SchemeTheory.Etale.UniversalHomeomorphismSections
public import Nyll.SchemeTheory.Etale.AffineBaseChangeProperties
public import Nyll.SchemeTheory.Etale.HenselianLocalSection
public import Nyll.SchemeTheory.Etale.GeometricFiberBound
public import Nyll.SchemeTheory.Etale.IntegralRefinement
public import Nyll.SchemeTheory.Etale.LocalResidueFieldExtension
public import Nyll.SchemeTheory.Etale.ResidueFieldPushout
public import Nyll.SchemeTheory.Etale.ClosedFiberBaseChange
public import Nyll.SchemeTheory.Etale.PurelyInseparableFiniteFactor
public import Nyll.SchemeTheory.Etale.FiniteRadicialLocalSplitting
public import Nyll.SchemeTheory.Etale.FiniteRadicialSplittingAlgebra
public import Nyll.SchemeTheory.Etale.FiniteRadicialSplittingCover
public import Nyll.SchemeTheory.Etale.MaximalSectionExtension
public import Nyll.SchemeTheory.Etale.AffineFiniteSubalgebraRefinement
public import Nyll.SchemeTheory.Etale.LocalFactorBaseChange
public import Nyll.SchemeTheory.Etale.AffineChartFiniteSubalgebra
public import Nyll.SchemeTheory.Etale.LocalFactorOpenCover
public import Nyll.SchemeTheory.Etale.FiniteRefinement
public import Nyll.SchemeTheory.Etale.FiniteGeometricPoints
public import Nyll.SchemeTheory.Etale.HenselianLocalGeometricSection
public import Nyll.SchemeTheory.Etale.FiniteStrictLocalGeometricSection
public import Nyll.SchemeTheory.Etale.Frobenius
public import Nyll.SchemeTheory.Etale.FiniteStrictLocalSchemeGeometricSection
public import Nyll.SchemeTheory.Etale.FrobeniusSquare
public import Nyll.SchemeTheory.Etale.ProperFiberIsomorphismNeighborhood

/- Canonical aggregate for SchemeTheory.Etale. -/
