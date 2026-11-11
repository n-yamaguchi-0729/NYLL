/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.FixedComponentCohomology
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.EtaleCohomology.Frobenius.GeometricComponentTrace
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2ArithmeticPower
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2
public import Nyll.SchemeTheory.Divisors.FixedComponentIsomorphism
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.LinearAlgebra.Trace

/-!
# Actual H2 Frobenius action on a fixed geometric component

The actual inverse-arithmetic automorphism of a fixed component has
the original m-th arithmetic power on the base. The original degree
calculation therefore makes its H2 action multiplication by q^m.
The proved comparison of the original component diagonal with the
actual geometric restriction transfers this action to the same
endomorphism whose actual fixed points are counted componentwise.
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
/-- The actual geometric Frobenius restriction acts by q^m on the
original H2 of each component fixed by its m-th power. -/
theorem nativeFrobeniusFixedComponentH2 (m : ℕ) (Z : irreducibleComponents Y)
    (hZ : Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z) :
    rationalEllAdicCohomologyPullback ℓ
        (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z hZ) 2 =
      (Fintype.card k ^ m) • (1 : Module.End ℚ_[ℓ]
        (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.1 Z.2) 2)) := by
  have : IsNoetherian Y := smoothProperScheme_isNoetherian g
  rw [← rationalEllAdicComponentDiagonal_eq_geometricFrobenius k K X ℓ
    (smoothSchemeDomainStalks g) 2 m Z hZ,
    rationalEllAdicComponentDiagonal_eq_fixedComponentPullback ℓ
      (inverseArithmeticFrobeniusPowerIso k K X m) 2 Z hZ]
  let C := (Y).reducedIrreducibleComponent Z.1 Z.2
  let d := (Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ g
  have : IsProper d := reducedIrreducibleComponent_isProper g Z
  have : SmoothOfRelativeDimension 1 d := reducedIrreducibleComponent_smooth_one g Z
  let algKC : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField d).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve d
  let e := inverseArithmeticFrobeniusPowerIso k K X m
  let a := Spec.map (CommRingCat.ofHom
    ((FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm ^ m).toRingHom)
  have he : e.hom ≫ g = g ≫ a :=
    Scheme.constantFieldTwist_snd k K X
      ((FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm ^ m)
  exact M.nativeRationalEllAdicH2_inverseArithmeticPower k K ℓ hℓ m
    (Scheme.reducedIrreducibleFixedComponentIso e Z hZ)
    (Scheme.reducedIrreducibleFixedComponentIso_toBase e Z hZ g a he)

include hℓ in
/-- The actual component restriction has original H2 trace q^m,
with all finite-dimensional and rank-one facts supplied by that curve. -/
theorem nativeFrobeniusFixedComponentH2_trace (m : ℕ) (Z : irreducibleComponents Y)
    (hZ : Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z) :
    LinearMap.trace ℚ_[ℓ]
        (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.1 Z.2) 2)
        (rationalEllAdicCohomologyPullback ℓ
          (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z hZ) 2) =
      (Fintype.card k : ℚ_[ℓ]) ^ m := by
  let d := (Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ g
  have : IsProper d := reducedIrreducibleComponent_isProper g Z
  have : SmoothOfRelativeDimension 1 d := reducedIrreducibleComponent_smooth_one g Z
  have : FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.1 Z.2) 2) :=
    nativeRationalEllAdicH2_finiteDimensional K d ℓ hℓ
  rw [nativeFrobeniusFixedComponentH2 k K X ℓ hℓ m Z hZ,
    map_nsmul, LinearMap.trace_one, nativeRationalEllAdicH2_finrank K d ℓ hℓ,
    Nat.cast_one, nsmul_eq_mul, mul_one, Nat.cast_pow]

end AlgebraicGeometry.SmoothProperCurve
