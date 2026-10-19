/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Norm.Defs
import Nyll.SchemeTheory.RingTheory.NormIdentities
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR

/-!
# Place ord norm sub eq ord eval
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_norm_sub_eq_ord_eval

open Polynomial AlgebraicCurve

namespace S09NR

section Ord

open AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra F F']
  [Module.Finite F F']

theorem ord_norm_sub_eq (v : Place K F) (Q : Polynomial v.toValuationSubring) {x : F'}
    (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x)
    (hdeg : (minpoly F x).natDegree = Module.finrank F F') (b : v.toValuationSubring) :
    v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring)
      : F) := by
  have h1 : x - algebraMap F F' (b : F) = -(algebraMap F F' (b : F) - x) := (neg_sub _ _).symm
  have h2 : Algebra.norm F (-(algebraMap F F' (b : F) - x))
      = (-1) ^ Module.finrank F F' * Algebra.norm F (algebraMap F F' (b : F) - x) := by
    have hneg1 : (-1 : F') = algebraMap F F' (-1) := by rw [map_neg, map_one]
    rw [neg_eq_neg_one_mul, map_mul, hneg1, Algebra.norm_algebraMap]
  have h3 : ((Q.eval b : v.toValuationSubring) : F) = (minpoly F x).eval (b : F) := by
    rw [← hQ, eval_map]
    exact (eval₂_at_apply (algebraMap v.toValuationSubring F) b).symm
  rw [h1, h2, Algebra.norm_algebraMap_sub_eq_minpoly_eval x hdeg, h3]
  rcases neg_one_pow_eq_or F (Module.finrank F F') with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, Place.ord_neg]

end Ord

end S09NR

theorem _root_.AlgebraicCurve.Place.ord_norm_sub_eq_ord_eval {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra F F'] [Module.Finite F F'] (v : Place K F) (Q : Polynomial
  v.toValuationSubring) {x : F'} (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x)
  (hdeg : (minpoly F x).natDegree = Module.finrank F F') (b : v.toValuationSubring) : v.ord
  (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F) :=
  by
  exact S09NR.ord_norm_sub_eq v Q hQ hdeg b
end AlgebraicCurves.Places.Proofs.Place_ord_norm_sub_eq_ord_eval
end ProofImplementation
