/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.EtaleCohomology.Classical.ComponentCohomologyTrace
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.JacobianVarieties.Kummer.SmoothProperComponentCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual component traces of smooth proper curves

The original smooth proper geometry supplies every hypothesis of the
cohomological component trace computation. The statement applies to
all three original groups in the curve trace formula, without an extra
finiteness or decomposition assumption. The Frobenius specialization
uses the literal geometric base change of the original finite-field
curve and retains its original Frobenius operator in every power.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicGeometry.SmoothProperCurve

section Curve

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

include c hℓ in
/-- Actual finite-dimensionality on each original component supplies
the trace decomposition for every original curve-cohomology degree. -/
theorem nativeRationalCohomology_trace_components (e : X ≅ X)
    (i : ℕ) (hi : i ≤ 2) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ X i)
        (rationalEllAdicCohomologyPullback ℓ e.hom i) =
      ∑ᶠ Z : {Z : irreducibleComponents X // Scheme.irreducibleComponentsIsoEquiv e Z = Z},
        LinearMap.trace ℚ_[ℓ]
          (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.val.1 Z.val.2) i)
          (rationalEllAdicComponentDiagonal e ℓ i Z.val) := by
  have : IsNoetherian X := smoothProperScheme_isNoetherian c
  have (Z : irreducibleComponents X) : FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) i) :=
    nativeRationalComponent_finiteDimensional_of_le_two K c ℓ hℓ i hi Z
  exact rationalEllAdicCohomology_trace_eq_sum_fixed_components e ℓ
    (smoothSchemeDomainStalks c) i

end Curve

section Frobenius

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "Y" => pullback (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "g" => pullback.snd (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)

include hℓ in
/-- The original finite-field curve's actual Frobenius powers have
their original H0, H1, and H2 traces on precisely the fixed geometric
components. All component finiteness is proved from the same curve. -/
theorem nativeFrobeniusRationalCohomology_trace_components (i m : ℕ) (hi : i ≤ 2) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y i)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ i) ^ m) =
      ∑ᶠ Z : {Z : irreducibleComponents Y //
          Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z},
        LinearMap.trace ℚ_[ℓ]
          (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.val.1 Z.val.2) i)
          (rationalEllAdicComponentDiagonal (inverseArithmeticFrobeniusPowerIso k K X m)
            ℓ i Z.val) := by
  have : IsNoetherian Y := smoothProperScheme_isNoetherian g
  have (Z : irreducibleComponents Y) : FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.1 Z.2) i) :=
    nativeRationalComponent_finiteDimensional_of_le_two K g ℓ hℓ i hi Z
  exact finiteFieldFrobeniusRationalEllAdicCohomology_trace_components k K X ℓ
    (smoothSchemeDomainStalks g) i m

end Frobenius

end AlgebraicGeometry.SmoothProperCurve
