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

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.BaseChange.All
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Bases.All
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.All
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.EqGenusFFEllSubEllEq
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.All
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusFFSubOneEqSplittingFieldDvdOrd
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusFFSubOneEqSplittingFieldDvdOrdNatCastNeZero
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusRiemannIndexCurve
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Index.All
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LocalSections.All
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.OpenBoundary
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.All
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Tsen
