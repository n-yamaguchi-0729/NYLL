/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Evaluation
public import Nyll.AlgebraicCurves.Divisors.KummerRootEvaluation
public import Nyll.AlgebraicCurves.Places.Degree.IsRationalAlgClosed
public import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation

/-!
# The actual unit given by a division-divisor evaluation

Disjointness and the two original divisor equations make the
evaluation quotient a genuine unit. Its original power is computed
by Weil reciprocity. The unit can therefore be inserted into the
actual root-fiber equivalence without a nonvanishing or root premise.
The finite function-field structure ensures that every residue place is
rational over the algebraically closed constant field.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve.Divisor

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  (n : ℕ) (D E B : Divisor K F) (f g : F) (hf : f ≠ 0) (hg : g ≠ 0)
  (hfdiv : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
  (hgdiv : ∀ v : Place K F, v.ord g = (n : ℤ) * E v - B v)
  (hDE : ∀ v : Place K F, D v = 0 ∨ E v = 0)
  (hDB : ∀ v : Place K F, D v = 0 ∨ B v = 0)

include hf hg hfdiv hgdiv hDE hDB in
/-- The actual evaluation root is nonzero by the original order
equations and disjoint supports. -/
theorem kummerEvaluationQuotient_ne_zero : evalFun f E / evalFun g D ≠ 0 := by
  have hfE : ∀ v ∈ E.support, v.evalAt f ≠ 0 := by
    intro v hv
    apply v.evalAt_ne_zero v.isRational_of_isAlgClosed hf
    rw [hfdiv v, (hDE v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
  have hgD : ∀ v ∈ D.support, v.evalAt g ≠ 0 := by
    intro v hv
    apply v.evalAt_ne_zero v.isRational_of_isAlgClosed hg
    rw [hgdiv v, (hDE v).resolve_left (Finsupp.mem_support_iff.mp hv),
      (hDB v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero, sub_self]
  exact div_ne_zero (evalFun_ne_zero hfE) (evalFun_ne_zero hgD)

/-- The same explicit evaluation quotient as an actual unit. -/
def kummerEvaluationUnit : Kˣ :=
  Units.mk0 (evalFun f E / evalFun g D)
    (kummerEvaluationQuotient_ne_zero n D E B f g hf hg hfdiv hgdiv hDE hDB)

theorem kummerEvaluationUnit_val :
    (kummerEvaluationUnit n D E B f g hf hg hfdiv hgdiv hDE hDB : K) =
      evalFun f E / evalFun g D :=
  rfl

variable [HasPrincipalDivisors K F]

/-- The original divisor reciprocity theorem proves the power of
this actual unit; it is not an extra root-equation hypothesis. -/
theorem kummerEvaluationUnit_pow :
    (kummerEvaluationUnit n D E B f g hf hg hfdiv hgdiv hDE hDB : K) ^ n =
      evalFun f B :=
  evaluation_quotient_pow n D E B f g hf hg hfdiv hgdiv hDE hDB

end AlgebraicCurve.Divisor
