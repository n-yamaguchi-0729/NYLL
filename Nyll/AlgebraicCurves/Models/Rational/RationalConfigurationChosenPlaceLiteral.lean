/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionValues
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders

/-! # The retained arithmetic cusp place is the literal original rational place

The existing all-order comparison determines the original valuation ring.
Consequently the arithmetic place already used by cusp specialization is equal
to the literal place of the original homogeneous point. Its finite-extension
value is thus the value used by the actual square-cover boundary labels.
-/

noncomputable section
open AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
  [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]

/-- All normalized orders identify the retained arithmetic place with the
literal place of this same original rational label. -/
theorem rationalConfiguration_arithmeticPlace_eq_literal
    (s : Finset (Projectivization k (k × k))) (a : s)
    (V : Place k (RatFunc k))
    (hord : ∀ z : RatFunc k,
      (rationalConfigurationBoundaryPlace k κ s a).val.ord
        (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z) :
    V = literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero := by
  have heq (z : RatFunc k) : V.ord z =
      (literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero).ord z :=
    (hord z).symm.trans (rationalConfigurationBoundaryPlace_coefficient_orders
      k κ s a z)
  apply Place.ext
  ext z
  rcases eq_or_ne z 0 with rfl | hz
  · exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [V.mem_iff_ord_nonneg hz,
      (literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero).mem_iff_ord_nonneg hz,
      heq z]

/-- The exact choice used by the original normalization-prime decomposition
and cusp specialization has the literal original rational valuation ring. -/
theorem rationalConfiguration_chosen_arithmeticPlace_eq_literal
    [IsAlgClosed κ] (s : Finset (Projectivization k (k × k))) (a : s) :
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
      (rationalConfigurationBoundaryPlace k κ s a)).choose =
        literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero := by
  apply rationalConfiguration_arithmeticPlace_eq_literal k κ s a
  exact (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
    (rationalConfigurationBoundaryPlace k κ s a)).choose_spec.2

/-- The already retained arithmetic place evaluates the unchanged function
compatibly with its actual boundary place over the selected finite constants. -/
theorem rationalConfiguration_retainedPlace_finiteExtension_evalAt
    (E : Type) [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k))) (a : s)
    (V : Place k (RatFunc k))
    (hord : ∀ z : RatFunc k,
      (rationalConfigurationBoundaryPlace k κ s a).val.ord
        (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z)
    (f : RatFunc k) (hf : f ≠ 0) :
    (rationalConfigurationBoundaryPlace k E s a).val.evalAt
        (algebraMap (RatFunc k) (RatFunc E) f) = algebraMap k E (V.evalAt f) := by
  rw [rationalConfiguration_arithmeticPlace_eq_literal k κ s a V hord]
  exact rationalConfigurationBoundaryPlace_coefficient_evalAt k E s a f hf

/-- A root of the retained arithmetic cusp value is a root of the actual
finite-base boundary value, without choosing another root or another place. -/
theorem rationalConfiguration_retainedPlace_finiteExtension_square_value
    (E : Type) [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k))) (a : s)
    (V : Place k (RatFunc k))
    (hord : ∀ z : RatFunc k,
      (rationalConfigurationBoundaryPlace k κ s a).val.ord
        (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z)
    (f : RatFunc k) (hf : f ≠ 0) (r : E)
    (hr : r ^ 2 = algebraMap k E (V.evalAt f)) :
    r ^ 2 = (rationalConfigurationBoundaryPlace k E s a).val.evalAt
      (algebraMap (RatFunc k) (RatFunc E) f) :=
  hr.trans (rationalConfiguration_retainedPlace_finiteExtension_evalAt
    k κ E s a V hord f hf).symm

end AlgebraicGeometry.ProjSpace

