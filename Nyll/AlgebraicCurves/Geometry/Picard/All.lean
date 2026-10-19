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

import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.All
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.All
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicPointsEquivariance
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicallyClosedPointHom
import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.All
import Nyll.AlgebraicCurves.Geometry.Picard.Cohomology.All
import Nyll.AlgebraicCurves.Geometry.Picard.CompEqOpenImmersion
import Nyll.AlgebraicCurves.Geometry.Picard.Deformation.All
import Nyll.AlgebraicCurves.Geometry.Picard.Divisors.All
import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.All
import Nyll.AlgebraicCurves.Geometry.Picard.Functor.All
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.All
import Nyll.AlgebraicCurves.Geometry.Picard.IsClosedSetOfFibreModuleIsoUnit
import Nyll.AlgebraicCurves.Geometry.Picard.IsFiniteToBaseGeometricFibreGenusEqZero
import Nyll.AlgebraicCurves.Geometry.Picard.IsProperGeometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Picard.LFPFgIsoPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Poincare.All
import Nyll.AlgebraicCurves.Geometry.Picard.PullbackSectionIdealPowModuleIso
import Nyll.AlgebraicCurves.Geometry.Picard.PushforwardPullbackIso
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.All
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.All
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.All
import Nyll.AlgebraicCurves.Geometry.Picard.Theta.All
