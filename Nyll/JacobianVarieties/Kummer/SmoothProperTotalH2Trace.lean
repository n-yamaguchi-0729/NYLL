/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ComponentH0Trace
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.JacobianVarieties.Kummer.SmoothProperComponentH2Frobenius
public import Nyll.JacobianVarieties.Kummer.SmoothProperGeometricComponentTrace
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Original H0 and H2 traces for every smooth proper finite-field curve

Every actual fixed geometric component contributes q^m to the original
H2 trace. The original finite component decomposition gives the total
H2 trace as q^m times the actual fixed-component count. Together with
the original H0 calculation this determines both outer terms of the
three-term formula, without a geometric connectedness assumption.
The remaining H1 trace is kept as the actual original endomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicGeometry.SmoothProperCurve

variable (k K : Type) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] (X : Scheme)
  [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "Y" => pullback (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "g" => pullback.snd (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)

include hℓ in
/-- The original H2 trace is q^m times the number of actual
components fixed by the original inverse-arithmetic permutation. -/
theorem nativeFrobeniusRationalH2_trace_eq_fixedComponentCard (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 2)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m) =
      (Nat.card {Z : irreducibleComponents Y //
        Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z} :
          ℚ_[ℓ]) * (Fintype.card k : ℚ_[ℓ]) ^ m := by
  classical
  let : Fintype (irreducibleComponents Y) := smoothProperComponentsFintype g
  let B := {Z : irreducibleComponents Y //
    Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z}
  calc
    _ = ∑ᶠ Z : B, (Fintype.card k : ℚ_[ℓ]) ^ m := by
      rw [nativeFrobeniusRationalCohomology_trace_geometricComponents k K X ℓ hℓ 2 m le_rfl]
      apply finsum_congr
      intro Z
      exact nativeFrobeniusFixedComponentH2_trace k K X ℓ hℓ m Z.val Z.property
    _ = (Nat.card B : ℚ_[ℓ]) * (Fintype.card k : ℚ_[ℓ]) ^ m := by
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
        Nat.card_eq_fintype_card, nsmul_eq_mul]

include hℓ in
/-- The same original H2 trace counts components fixed by the
actual geometric Frobenius power on their actual underlying subsets. -/
theorem nativeFrobeniusRationalH2_trace_eq_geometricComponentCard (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 2)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m) =
      (Nat.card {Z : irreducibleComponents Y //
        ((End.of (Scheme.constantBaseChangeFrobenius k K X)) ^ m).asHom '' Z.1 = Z.1} :
          ℚ_[ℓ]) * (Fintype.card k : ℚ_[ℓ]) ^ m := by
  have : IsNoetherian Y := smoothProperScheme_isNoetherian g
  rw [nativeFrobeniusRationalH2_trace_eq_fixedComponentCard k K X ℓ hℓ m]
  have hcard := (finiteFieldFrobeniusRationalH0_trace_eq_componentCard k K X ℓ
    (smoothSchemeDomainStalks g) m).symm.trans
      (nativeFrobeniusRationalH0_trace_eq_geometricComponentCard k K X ℓ m)
  exact congrArg (fun r : ℚ_[ℓ] => r * (Fintype.card k : ℚ_[ℓ]) ^ m) hcard

include hℓ in
/-- The actual outer terms of the original three-term trace formula
are completely determined by the actual fixed-component count. -/
theorem nativeFrobeniusRationalCohomology_alternatingTrace_outerTerms (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 0)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 0) ^ m) -
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 1)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 1) ^ m) +
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 2)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m) =
      (Nat.card {Z : irreducibleComponents Y //
        ((End.of (Scheme.constantBaseChangeFrobenius k K X)) ^ m).asHom '' Z.1 = Z.1} :
          ℚ_[ℓ]) * (1 + (Fintype.card k : ℚ_[ℓ]) ^ m) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 1)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 1) ^ m) := by
  rw [nativeFrobeniusRationalH0_trace_eq_geometricComponentCard k K X ℓ m,
    nativeFrobeniusRationalH2_trace_eq_geometricComponentCard k K X ℓ hℓ m,
    mul_add, mul_one, sub_add_eq_add_sub]

end AlgebraicGeometry.SmoothProperCurve
