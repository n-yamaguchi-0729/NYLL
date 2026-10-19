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

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Action
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.EndDegree
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Fibre
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.KernelPair
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Translation
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.MultiplicationMorphisms
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangMap
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangPointFormula
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLang
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLangPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLangNorm
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangIterate
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLangPowers
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsBaseChange

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.CanonicalModelFactorization
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsPullback
