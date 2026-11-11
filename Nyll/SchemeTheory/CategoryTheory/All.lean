/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.CategoryTheory.ModuleEndomorphismPowers

public import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints
public import Nyll.SchemeTheory.CategoryTheory.CokernelNsmulQuotient
public import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
public import Nyll.SchemeTheory.CategoryTheory.CommGroupPoints
public import Nyll.SchemeTheory.CategoryTheory.DescentComparison
public import Nyll.SchemeTheory.CategoryTheory.FilteredColimitFiniteDescent
public import Nyll.SchemeTheory.CategoryTheory.FunctorCategoryExactness
public import Nyll.SchemeTheory.CategoryTheory.ModuleCatTensorExtension
public import Nyll.SchemeTheory.CategoryTheory.MonoidalCategoryIsoTensorIsoTensorUnit
public import Nyll.SchemeTheory.CategoryTheory.MonoidalClosedIsoEvAppIsoCurryBraidingEv
public import Nyll.SchemeTheory.CategoryTheory.MorphismPropertyWidePullbackBase
public import Nyll.SchemeTheory.CategoryTheory.OverPullbackLeft
public import Nyll.SchemeTheory.CategoryTheory.OverTotalLocalBijection
public import Nyll.SchemeTheory.CategoryTheory.OverTotalMap
public import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
public import Nyll.SchemeTheory.CategoryTheory.OverTotalRepresentation
public import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates
public import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap
public import Nyll.SchemeTheory.CategoryTheory.PresheafDirectSum
public import Nyll.SchemeTheory.CategoryTheory.PresheafModulePushforward
public import Nyll.SchemeTheory.CategoryTheory.PseudofunctorDescentDataIsoToDescentDataObj
public import Nyll.SchemeTheory.CategoryTheory.Pullback
public import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupBaseChange
public import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupDiagram
public import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIdentity
public import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso
public import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupPullbackIso
public import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupTargetIso
public import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups
public import Nyll.SchemeTheory.CategoryTheory.SheafificationLocalLifts
public import Nyll.SchemeTheory.CategoryTheory.ModuleColimitGenerator

/- Canonical aggregate for SchemeTheory.CategoryTheory. -/

public import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparison
public import Nyll.SchemeTheory.CategoryTheory.EquivariantScalarTowerComparison
public import Nyll.SchemeTheory.CategoryTheory.ScalarTowerMapComparison
public import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparisonExistence
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.CategoryTheory.EqualizerPoints
public import Nyll.SchemeTheory.CategoryTheory.FiniteActionGraphs
public import Nyll.SchemeTheory.CategoryTheory.TensorInverseIso

/-!
# Categorical tools for scheme descent

This aggregate exposes descent comparisons, module tensor extensions, over-category
pullback, and total presheaves over a base.
-/
