/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.All
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.All

/-!
# Branched coverings of the projective line over the integers

Formalization of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).

The present sources cover integral coordinate changes from Lemma 2.3, the
coordinate calculation in Lemma 2.4, the arithmetic six-section bound in
Corollary 2.7, and the connected finite etale quadratic cover used in
Proposition 2.5. Its coordinate algebra is an integral domain, free of rank
two, and it gives a continuous quadratic quotient of the affine fundamental
group. The construction reuses the existing adjoined-root etale criterion
and Galois-category results from the etale fundamental group library.

The actual projective open `D₊(T₁) ∩ D₊(v*T₀-u*T₁)` is identified with
`Spec ℤ[t, 1/(v*t-u)]` by a constructed scheme isomorphism, compatible with
the maps to the projective line.

The section and intersection-multiplicity comparisons for arbitrary
primitive coordinates, projective coordinate changes, the prosolvable
criterion of Theorem 2.6, and the finite simple quotient exclusions of
Theorems 3.1 and 3.6 remain to be formalized here.
-/
