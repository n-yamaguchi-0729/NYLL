/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.OpenNeighborhoods
public import Nyll.SchemeTheory.Affine.AffineFppfComparison
public import Nyll.SchemeTheory.Affine.AffineFppfComparisonUnit
public import Nyll.SchemeTheory.Affine.AffinizationDescent
public import Nyll.SchemeTheory.Affine.ChartStalkLocalization
public import Nyll.SchemeTheory.Affine.ClosedBaseChangeSections
public import Nyll.SchemeTheory.Affine.CoefficientPullbackSquare
public import Nyll.SchemeTheory.Affine.ConnectedOfGlobalSections
public import Nyll.SchemeTheory.Affine.FaithfullyFlatSectionSurjectivity
public import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebra
public import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebraBaseChange
public import Nyll.SchemeTheory.Affine.FiniteSchemeScalarFunctor
public import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
public import Nyll.SchemeTheory.Affine.FiniteSchemeScalarQuotient
public import Nyll.SchemeTheory.Affine.FiniteSchemeUnitRestriction
public import Nyll.SchemeTheory.Affine.FiniteSchemeUnitRestrictionGeometry
public import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
public import Nyll.SchemeTheory.Affine.FlatBaseChangeSections
public import Nyll.SchemeTheory.Affine.FlatMinimalPrime
public import Nyll.SchemeTheory.Affine.GeometricPointLocalization
public import Nyll.SchemeTheory.Affine.GeometricallyConnectedOfGlobalSections
public import Nyll.SchemeTheory.Affine.HomeomorphismIdempotentSections
public import Nyll.SchemeTheory.Affine.PrimePairHartogs
public import Nyll.SchemeTheory.Affine.PullbackSectionsPushout
public import Nyll.SchemeTheory.Affine.RegularPairHartogs
public import Nyll.SchemeTheory.Affine.RegularSection
public import Nyll.SchemeTheory.Affine.RelativeSectionsOnSpectra
public import Nyll.SchemeTheory.Affine.SeparatedIntersections
public import Nyll.SchemeTheory.Affine.SpecBaseChangeSectionsMap
public import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections
public import Nyll.SchemeTheory.Affine.SpecSectionMap
public import Nyll.SchemeTheory.Affine.StalkBaseChange
public import Nyll.SchemeTheory.Affine.StalkBaseChangeSections
public import Nyll.SchemeTheory.Affine.StalkFractionField
public import Nyll.SchemeTheory.Affine.StalkLocalization
public import Nyll.SchemeTheory.Affine.SurjectiveSectionPushout
public import Nyll.SchemeTheory.Affine.UnramifiedGenericFiber
public import Nyll.SchemeTheory.Affine.WeilRestriction.All

/- Canonical aggregate for SchemeTheory.Affine. -/

/-!
# Affine scheme infrastructure

This facade collects affine-over-base colimits, affine morphism properties,
flat minimal-prime control, and geometric irreducibility of affine schemes.
-/
