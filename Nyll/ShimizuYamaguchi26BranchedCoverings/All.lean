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

The current additions are draft sources awaiting Lean validation. They supply
integral coordinate changes from Lemma 2.3, the
coordinate calculation in Lemma 2.4, the arithmetic six-section bound in
Corollary 2.7, and the connected finite etale quadratic cover used in
Proposition 2.5. Its coordinate algebra is an integral domain, free of rank
two, and it gives a continuous quadratic quotient of the affine fundamental
group. The construction reuses the existing adjoined-root etale criterion
and Galois-category results from the etale fundamental group library.

The actual projective open `D₊(T₁) ∩ D₊(v*T₀-u*T₁)` is identified with
`Spec ℤ[t, 1/(v*t-u)]` by a constructed scheme isomorphism, compatible with
the maps to the projective line. Bézout coefficients construct projective
scheme automorphisms taking any primitive integral linear equation to the
equation at infinity. Restricting these automorphisms gives affine models
for arbitrary pairs of linear equations with primitive first coordinates;
the determinant is the transformed denominator coefficient. If both pairs
are primitive and their determinant is nonzero and divisible by four, the
continuous quadratic quotient is constructed on every open inside their
common complement.

On the infinity chart, the intersection algebra defined by `w` and `v-u*w`
is explicitly identified with `R/(v)`. Over a DVR its module length is the
additive valuation of `v`. Localizing the polynomial chart at its actual
closed-point ideal preserves this intersection quotient, and its length
over that local ring is computed. The projective chart/stalk and primitive
section-image identifications remain to be supplied.

The section and intersection-multiplicity comparisons for arbitrary
primitive coordinates, the prosolvable criterion of Theorem 2.6, and the
finite simple quotient exclusions of
Theorems 3.1 and 3.6 remain to be formalized here.
-/
