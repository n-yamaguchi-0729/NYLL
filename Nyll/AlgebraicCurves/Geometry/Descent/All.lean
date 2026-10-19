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

import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction
import Nyll.AlgebraicCurves.Geometry.Descent.FppfGmRepresentable
import Nyll.AlgebraicCurves.Geometry.Descent.DescentActionEffectiveFiniteEtale
import Nyll.AlgebraicCurves.Geometry.Descent.DescentActionEffectiveFiniteEtaleOrbit
import Nyll.AlgebraicCurves.Geometry.Descent.DescentActionEffectivePullback

import Nyll.AlgebraicCurves.Geometry.Descent.FaithfullyFlatProperties
import Nyll.AlgebraicCurves.Geometry.Descent.FiniteFaithfullyFlat
import Nyll.AlgebraicCurves.Geometry.Descent.GlobalRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.FppfCoverRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.GroupGlobalRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.GroupOfMatching
import Nyll.AlgebraicCurves.Geometry.Descent.RepresentableMatching
import Nyll.AlgebraicCurves.Geometry.Descent.FaithfullyFlatFiniteTypeGeometry
import Nyll.AlgebraicCurves.Geometry.Descent.NaturalRepresentationDescent
import Nyll.AlgebraicCurves.Geometry.Descent.SheafifiedLocalRepresentation
