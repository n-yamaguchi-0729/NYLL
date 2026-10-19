/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints
import Nyll.SchemeTheory.CategoryTheory.CokernelNsmulQuotient
import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Nyll.SchemeTheory.CategoryTheory.CommGroupPoints
import Nyll.SchemeTheory.CategoryTheory.DescentComparison
import Nyll.SchemeTheory.CategoryTheory.FilteredColimitFiniteDescent
import Nyll.SchemeTheory.CategoryTheory.FunctorCategoryExactness
import Nyll.SchemeTheory.CategoryTheory.ModuleCatTensorExtension
import Nyll.SchemeTheory.CategoryTheory.MonoidalCategoryIsoTensorIsoTensorUnit
import Nyll.SchemeTheory.CategoryTheory.MonoidalClosedIsoEvAppIsoCurryBraidingEv
import Nyll.SchemeTheory.CategoryTheory.MorphismPropertyWidePullbackBase
import Nyll.SchemeTheory.CategoryTheory.OverPullbackLeft
import Nyll.SchemeTheory.CategoryTheory.OverTotalLocalBijection
import Nyll.SchemeTheory.CategoryTheory.OverTotalMap
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.SchemeTheory.CategoryTheory.OverTotalRepresentation
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap
import Nyll.SchemeTheory.CategoryTheory.PresheafDirectSum
import Nyll.SchemeTheory.CategoryTheory.PresheafModulePushforward
import Nyll.SchemeTheory.CategoryTheory.PseudofunctorDescentDataIsoToDescentDataObj
import Nyll.SchemeTheory.CategoryTheory.Pullback
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupBaseChange
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupDiagram
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIdentity
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupPullbackIso
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupTargetIso
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups
import Nyll.SchemeTheory.CategoryTheory.SheafificationLocalLifts
import Nyll.SchemeTheory.CategoryTheory.ModuleColimitGenerator

/- Canonical aggregate for SchemeTheory.CategoryTheory. -/

import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparison
import Nyll.SchemeTheory.CategoryTheory.EquivariantScalarTowerComparison
import Nyll.SchemeTheory.CategoryTheory.ScalarTowerMapComparison
import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparisonExistence

/-!
# Categorical tools for scheme descent

This aggregate exposes descent comparisons, module tensor extensions, over-category
pullback, and total presheaves over a base.
-/
