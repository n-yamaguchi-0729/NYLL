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

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.All
import Nyll.AlgebraicCurves.Geometry.Curves.All
import Nyll.AlgebraicCurves.Geometry.Deformation.All
import Nyll.AlgebraicCurves.Geometry.Descent.All
import Nyll.AlgebraicCurves.Geometry.Picard.All
import Nyll.AlgebraicCurves.Geometry.Projective.All
import Nyll.AlgebraicCurves.Geometry.AlgHomEqRestrictAlongEq
import Nyll.AlgebraicCurves.Geometry.NonzeroDifferential
import Nyll.AlgebraicCurves.Geometry.BoundedTwoCochainLocalCoboundaries
import Nyll.AlgebraicCurves.Geometry.CoboundaryAtInfinitySmallExtension
import Nyll.AlgebraicCurves.Geometry.DiscSectionsLocalityHenselSections
import Nyll.AlgebraicCurves.Geometry.InjectiveEllSubSumSingleEqZero
import Nyll.AlgebraicCurves.Geometry.IntDegreeAddOneSubLeEll
import Nyll.AlgebraicCurves.Geometry.IsRationalMemEvalAtEqAlgHom
import Nyll.AlgebraicCurves.Geometry.LocalCoboundarySmallExtension
import Nyll.AlgebraicCurves.Geometry.MulEqHochschildCoboundary
import Nyll.AlgebraicCurves.Geometry.FundamentalIdentityAlong
import Nyll.AlgebraicCurves.Geometry.InvSmulDEqZeroIffPowEq
import Nyll.AlgebraicCurves.Geometry.IsClosedSingletonNeGenericPoint
import Nyll.AlgebraicCurves.Geometry.MapNeZeroTame
import Nyll.AlgebraicCurves.Geometry.MemMulEval2Mem
import Nyll.AlgebraicCurves.Geometry.AlgEquivFunctionFieldIso
import Nyll.AlgebraicCurves.Geometry.OneLeDeg
import Nyll.AlgebraicCurves.Geometry.WeilReciprocity
import Nyll.AlgebraicCurves.Geometry.WeilReciprocityAlgClosed
import Nyll.AlgebraicCurves.Geometry.Schemes.All
import Nyll.AlgebraicCurves.Geometry.Sheaves.All
