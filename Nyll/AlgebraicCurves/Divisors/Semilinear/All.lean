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

import Nyll.AlgebraicCurves.Divisors.Semilinear.CorrespondenceSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.EqBaseAutEq
import Nyll.AlgebraicCurves.Divisors.Semilinear.EqSmulPlaceEq
import Nyll.AlgebraicCurves.Divisors.Semilinear.UniqueBaseAutEqSmulAlgebraMapEq
import Nyll.AlgebraicCurves.Divisors.Semilinear.UniqueMonoidHomBaseAutEqSmulAlgebraMapEq
import Nyll.AlgebraicCurves.Divisors.Semilinear.BaseAutEqConstantExtension
import Nyll.AlgebraicCurves.Divisors.Semilinear.InertiaDegSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.AlgAutSmulPlace
import Nyll.AlgebraicCurves.Divisors.Semilinear.OrdAlgebraMapSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.Pic0CorrespondenceSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.Pic0CorrespondenceSwapSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.PullbackAlongSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.PullbackSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.PushforwardAlongSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.PushforwardSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.RamificationIndexSmul
import Nyll.AlgebraicCurves.Divisors.Semilinear.RestrictSmul
