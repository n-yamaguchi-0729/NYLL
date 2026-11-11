/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.PlaneCurves.ConstantExtension
public import Nyll.SchemeTheory.PlaneCurves.CoordinateRing
public import Nyll.SchemeTheory.PlaneCurves.Dimension
public import Nyll.SchemeTheory.PlaneCurves.Geometric
public import Nyll.SchemeTheory.PlaneCurves.MonicChange
public import Nyll.SchemeTheory.PlaneCurves.MonicProjection
public import Nyll.SchemeTheory.PlaneCurves.NormalImpliesSimple
public import Nyll.SchemeTheory.PlaneCurves.NormalPoint
public import Nyll.SchemeTheory.PlaneCurves.PartialDerivatives
public import Nyll.SchemeTheory.PlaneCurves.RationalPoints
public import Nyll.SchemeTheory.PlaneCurves.SimpleImpliesNormal

/-!
# Affine plane curves

This facade collects coordinate rings, rational points, monic projections,
and the equivalence between simple and normal points on affine plane curves.
-/

/- Canonical aggregate for SchemeTheory.PlaneCurves. -/
