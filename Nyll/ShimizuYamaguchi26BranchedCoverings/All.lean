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
coordinate calculation in Lemma 2.4, and the finite free etale quadratic algebra
constructed in Proposition 2.5. They reuse the existing adjoined-root etale
criterion from the etale fundamental group library.

The comparison with projective-line divisors, connectedness of the quadratic
cover, the prosolvable criterion of Theorem 2.6, and the finite simple quotient
exclusions of Theorems 3.1 and 3.6 remain to be formalized here.
-/
