/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Places.Evaluation.DerivativeEvalEvalEvalAtNeZeroOrdSubEqOneEvalAtNeSeparable
import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteSimpleExtensions
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Separable

/-!
# Place derivative nonvanishing in characteristic zero
-/

namespace AlgebraicCurve.Place

theorem derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (hrat : ∀ w : Place K F, w.IsRational)
    {z y : F} (hz : Transcendental K z)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (Q : Place K F) (hzQ : z ∈ Q.toValuationSubring) (hyQ : y ∈ Q.toValuationSubring)
    (he : Q.ord (z - algebraMap K F (Q.evalAt z)) = 1)
    (hlead : G.leadingCoeff.eval (Q.evalAt z) ≠ 0)
    (hsep : ∀ Q' : Place K F, Q' ≠ Q → z ∈ Q'.toValuationSubring → Q'.evalAt z = Q.evalAt z →
      y ∈ Q'.toValuationSubring → Q'.evalAt y ≠ Q.evalAt y) :
    (Polynomial.derivative G).evalEval (Q.evalAt z) (Q.evalAt y) ≠ 0 := by
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({z} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental x₀ hz
  have hcz : CharZero (IntermediateField.adjoin K ({z} : Set F)) :=
    charZero_of_injective_algebraMap
      (algebraMap K (IntermediateField.adjoin K ({z} : Set F))).injective
  have hsepF : Algebra.IsSeparable (IntermediateField.adjoin K ({z} : Set F)) F :=
    Algebra.IsSeparable.of_integral _ _
  exact derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne_of_isSeparable
    x₀ hrat hz G hGirr hG Q hzQ hyQ he hlead hsep

end AlgebraicCurve.Place
