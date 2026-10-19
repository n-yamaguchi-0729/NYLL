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

import Nyll.AlgebraicCurves.Divisors.ClassGroup.All
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.All
import Nyll.AlgebraicCurves.Divisors.Correspondences.All
import Nyll.AlgebraicCurves.Divisors.Degree.All
import Nyll.AlgebraicCurves.Divisors.Evaluation
import Nyll.AlgebraicCurves.Divisors.KummerRootEvaluation
import Nyll.AlgebraicCurves.Divisors.Maps.All
import Nyll.AlgebraicCurves.Divisors.Modulus.All
import Nyll.AlgebraicCurves.Divisors.Norm.All
import Nyll.AlgebraicCurves.Divisors.Principal.All
import Nyll.AlgebraicCurves.Divisors.Semilinear.All
