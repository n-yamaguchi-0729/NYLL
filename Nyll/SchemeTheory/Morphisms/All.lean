/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.AppLECongr
public import Nyll.SchemeTheory.Morphisms.ProperFiniteProjectiveCover
public import Nyll.SchemeTheory.Morphisms.ValuativeProperness
public import Nyll.SchemeTheory.Morphisms.OpenImmersionCriteria
public import Nyll.SchemeTheory.Morphisms.SmoothnessCriteria
public import Nyll.SchemeTheory.Morphisms.AffineCompactification
public import Nyll.SchemeTheory.Morphisms.PropernessCriteria
public import Nyll.SchemeTheory.Morphisms.SectionRigidity
public import Nyll.SchemeTheory.Morphisms.AffineNormalizationPushforward
public import Nyll.SchemeTheory.Morphisms.AlgebraicPointFiniteField
public import Nyll.SchemeTheory.Morphisms.ChowDatumProj
public import Nyll.SchemeTheory.Morphisms.ChowDatum
public import Nyll.SchemeTheory.Morphisms.ClosedImmersionLift
public import Nyll.SchemeTheory.Morphisms.ConstantTwist
public import Nyll.SchemeTheory.Morphisms.ConstantTwistTower
public import Nyll.SchemeTheory.Morphisms.DominantBaseChange
public import Nyll.SchemeTheory.Morphisms.EtalePostcomposition
public import Nyll.SchemeTheory.Morphisms.EtaleRadicial
public import Nyll.SchemeTheory.Morphisms.EtaleReduced
public import Nyll.SchemeTheory.Morphisms.FiberRank
public import Nyll.SchemeTheory.Morphisms.FiniteDescent
public import Nyll.SchemeTheory.Morphisms.FiniteEtaleGeometricallyReduced
public import Nyll.SchemeTheory.Morphisms.FiniteExtensionPoint
public import Nyll.SchemeTheory.Morphisms.FiniteAffinePoints
public import Nyll.SchemeTheory.Morphisms.FrobeniusFixedSchemePoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldPointPeriod
public import Nyll.SchemeTheory.Morphisms.FlatBaseChangeNormalization
public import Nyll.SchemeTheory.Morphisms.Frobenius
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Nyll.SchemeTheory.Morphisms.FrobeniusOver
public import Nyll.SchemeTheory.Morphisms.GeometricallyConnectedDescent
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralDescent
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralFieldDescent
public import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
public import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
public import Nyll.SchemeTheory.Morphisms.NoetherianProperFiberSections
public import Nyll.SchemeTheory.Morphisms.NormalizationFiniteFactor
public import Nyll.SchemeTheory.Morphisms.NormalizationFlatBaseChangeIso
public import Nyll.SchemeTheory.Morphisms.NormalizationPushforward
public import Nyll.SchemeTheory.Morphisms.OpenImmersionLocalization
public import Nyll.SchemeTheory.Morphisms.OpenImmersionQuotient
public import Nyll.SchemeTheory.Morphisms.OverPullbackDescent
public import Nyll.SchemeTheory.Morphisms.ProperHenselianClopenLift
public import Nyll.SchemeTheory.Morphisms.ProperHenselianClosedRestriction
public import Nyll.SchemeTheory.Morphisms.ProperHenselianSheafRestriction
public import Nyll.SchemeTheory.Morphisms.ProperIntegralHenselianConnectedFiber
public import Nyll.SchemeTheory.Morphisms.ProperIntegralHenselianSections
public import Nyll.SchemeTheory.Morphisms.ProperNormalization
public import Nyll.SchemeTheory.Morphisms.QuasiFinite
public import Nyll.SchemeTheory.Morphisms.RadicialDescent
public import Nyll.SchemeTheory.Morphisms.ResiduePointFixedness
public import Nyll.SchemeTheory.Morphisms.SeparatedQuasiCompactDescent
public import Nyll.SchemeTheory.Morphisms.SigmaPullback
public import Nyll.SchemeTheory.Morphisms.SmoothGeometricallyIntegral
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.SchemeTheory.Morphisms.StalkIdealPower
public import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
public import Nyll.SchemeTheory.Morphisms.UnramifiedPointRigidity
public import Nyll.SchemeTheory.Morphisms.AppTopPullbackMapEqAppTopPullbackFst
public import Nyll.SchemeTheory.Morphisms.ReducedSmooth
public import Nyll.SchemeTheory.Morphisms.Compactification
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.AffineBlowup
public import Nyll.SchemeTheory.Morphisms.AffineBlowupCharts
public import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverSeparablyClosed
public import Nyll.SchemeTheory.Morphisms.PurelyInseparableFieldExtension
public import Nyll.SchemeTheory.Morphisms.AffineBlowupExceptional

/- Canonical aggregate for SchemeTheory.Morphisms. -/
public import Nyll.SchemeTheory.Morphisms.OpenFlatLocus
public import Nyll.SchemeTheory.Morphisms.ProperBirationalIntegral
public import Nyll.SchemeTheory.Morphisms.ProperBirationalSeparated
public import Nyll.SchemeTheory.Morphisms.ProperGlobalSectionsFinite
public import Nyll.SchemeTheory.Morphisms.SmoothSectionLifting
public import Nyll.SchemeTheory.Morphisms.SmoothDimensionCharts
public import Nyll.SchemeTheory.Morphisms.SmoothRelativeDimension
public import Nyll.SchemeTheory.Morphisms.FiniteFieldFixedPoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldGeometricFixedPoints
public import Nyll.SchemeTheory.Morphisms.FiniteSchemePoints
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldRelativeFixedPoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldDegreeFixedPoints
public import Nyll.SchemeTheory.Morphisms.AffineFixedPointEqualizer
public import Nyll.SchemeTheory.Morphisms.FiniteFieldFrobeniusFixedScheme
public import Nyll.SchemeTheory.Morphisms.FiniteFieldRelativeFixedScheme
public import Nyll.SchemeTheory.Morphisms.FiniteFieldGlobalFixedScheme
public import Nyll.SchemeTheory.Morphisms.UnramifiedClosedStalkLength


public import Nyll.SchemeTheory.Morphisms.ProperIntegralGlobalSections
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponentPoints
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponentPointCount
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed

/-!
# Scheme morphisms

This facade collects the finite, flat, smooth, rank, reduced-etale, and
closed-immersion lemmas used by the finite étale and fundamental-group
developments.
-/
