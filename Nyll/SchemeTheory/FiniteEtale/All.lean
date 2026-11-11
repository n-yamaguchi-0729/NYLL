/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.LocalExtensionGluing
public import Nyll.SchemeTheory.FiniteEtale.FiniteEtaleMorphismNeighborhood
public import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
public import Nyll.SchemeTheory.FiniteEtale.AffineThickening
public import Nyll.SchemeTheory.FiniteEtale.AffineUniversalHomeomorphismModel
public import Nyll.SchemeTheory.FiniteEtale.Algebra.All
public import Nyll.SchemeTheory.FiniteEtale.Away.All
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.All
public import Nyll.SchemeTheory.FiniteEtale.ClopenFull
public import Nyll.SchemeTheory.FiniteEtale.ClopenPullback
public import Nyll.SchemeTheory.FiniteEtale.ConnectedFiberSections
public import Nyll.SchemeTheory.FiniteEtale.ConnectedFiberFullyFaithful
public import Nyll.SchemeTheory.FiniteEtale.MaximalOpenExtension
public import Nyll.SchemeTheory.FiniteEtale.FullOfSectionDescent
public import Nyll.SchemeTheory.FiniteEtale.DensePullback
public import Nyll.SchemeTheory.FiniteEtale.DVRUnramifiedExtension
public import Nyll.SchemeTheory.FiniteEtale.Forget.All
public import Nyll.SchemeTheory.FiniteEtale.Henselian.All
public import Nyll.SchemeTheory.FiniteEtale.Local.All
public import Nyll.SchemeTheory.FiniteEtale.LocalSplitting
public import Nyll.SchemeTheory.FiniteEtale.PullbackFaithful
public import Nyll.SchemeTheory.FiniteEtale.PullbackRepresentable
public import Nyll.SchemeTheory.FiniteEtale.RadicialDescentCocycle
public import Nyll.SchemeTheory.FiniteEtale.RadicialDescentIso
public import Nyll.SchemeTheory.FiniteEtale.RingCover
public import Nyll.SchemeTheory.FiniteEtale.ThickeningFullyFaithful
public import Nyll.SchemeTheory.FiniteEtale.ThickeningGluing
public import Nyll.SchemeTheory.FiniteEtale.UniversalHomeomorphismFullyFaithful
public import Nyll.SchemeTheory.FiniteEtale.SectionsDescent
public import Nyll.SchemeTheory.FiniteEtale.AffinizationExtension
public import Nyll.SchemeTheory.FiniteEtale.PointSections
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitHom
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitEquality
public import Nyll.SchemeTheory.FiniteEtale.FilteredColimitSpec
public import Nyll.SchemeTheory.FiniteEtale.AffineTransitionModel
public import Nyll.SchemeTheory.FiniteEtale.AffineTransitionCharts
public import Nyll.SchemeTheory.FiniteEtale.RelativeGluing
public import Nyll.SchemeTheory.FiniteEtale.TwoOpenGluing
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsomorphism
public import Nyll.SchemeTheory.FiniteEtale.AffineTransitionLocalModel
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitOpenEquations
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitFiniteCover
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoDescent
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoModels
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitOpenIsomorphisms
public import Nyll.SchemeTheory.FiniteEtale.AffineTransitionOverlapRecovery
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitGluingRelations
public import Nyll.SchemeTheory.FiniteEtale.RelativePullbackGluing
public import Nyll.SchemeTheory.FiniteEtale.RelativeOverlapFiniteness
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitRecoveredModel
public import Nyll.SchemeTheory.FiniteEtale.RawOverlapFiniteness
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitRawCharts
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitRawModel
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
public import Nyll.SchemeTheory.FiniteEtale.StrictLocalSections
public import Nyll.SchemeTheory.FiniteEtale.ProperClosedFiberFaithful
public import Nyll.SchemeTheory.FiniteEtale.ProperHenselianSections
public import Nyll.SchemeTheory.FiniteEtale.AffineUniversalHomeomorphismEquivalence
public import Nyll.SchemeTheory.FiniteEtale.IsoIsoPullbackClosedFibre
public import Nyll.SchemeTheory.FiniteEtale.PointSectionsBaseChange
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitEssentialSurjectivity
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitFiniteFamily


/-!
# Finite étale scheme theory

This facade collects affine Weil restriction, fpqc descent for finite étale
algebras, exactness of the forgetful functor, and étale schemes over a field.
-/

/- Canonical aggregate for SchemeTheory.FiniteEtale. -/
