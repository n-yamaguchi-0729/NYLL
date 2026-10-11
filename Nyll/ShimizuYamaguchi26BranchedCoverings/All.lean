/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.All

/-!
# Branched coverings of the projective line over the integers

Formalization of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).

The present sources cover integral coordinate changes from Lemma 2.3, the
coordinate calculation in Lemma 2.4, the arithmetic six-section bound in
Corollary 2.7, and the explicit connected finite etale quadratic cover of the
affine localization used in Proposition 2.5. The cover has integral source
and its coordinate algebra is free of rank two. The construction reuses the
existing adjoined-root etale criterion from the etale fundamental group library.

The comparison with projective-line divisors, the resulting quotient of the
etale fundamental group, the prosolvable criterion of Theorem 2.6, and the
finite simple quotient exclusions of Theorems 3.1 and 3.6 remain to be
formalized here.
-/
