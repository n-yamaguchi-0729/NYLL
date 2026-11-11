/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Divisors.FrobeniusComponentFixedCartierDegree
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalEdgeClass
public import Nyll.JacobianVarieties.Kummer.CurveGraphCycleDegree
public import Nyll.JacobianVarieties.Kummer.SmoothProperComponentH2Frobenius
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.Tactic.Ring

/-!
# Normalized diagonal degree on a fixed geometric component

The actual component graph meets its diagonal in the original fixed-point
Cartier divisor. Its degree counts those same fixed points. Removing the
two degree-one edge classes subtracts one and q^m, using the actual H²
action on this component. Individual components need not descend to k.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicGeometry.SmoothProperCurve

variable (k K : Type) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] (X : Scheme.{0})
  [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
  (m : ℕ) [NeZero m]

local notation "Y" => pullback (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "g" => pullback.snd (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)

/-- On each actual fixed geometric component, the normalized diagonal
has graph degree equal to its fixed-point count minus one minus q^m. -/
theorem nativeRationalDiagonalMiddleClass_frobeniusComponentGraph_degree
    (Z : irreducibleComponents Y)
    (hZ : Scheme.irreducibleComponentsIsoEquiv
      (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z) :
    let C := (Y).reducedIrreducibleComponent Z.1 Z.2
    let d := (Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ g
    let v := Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    let hv := Scheme.constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ
    let _ : IsProper d := reducedIrreducibleComponent_isProper g Z
    let _ : SmoothOfRelativeDimension 1 d := reducedIrreducibleComponent_smooth_one g Z
    let _ : Algebra K (Scheme.functionField C) :=
      (AlgebraicCurve.baseToFunctionField d).toAlgebra
    let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve d
    nativeRationalEllAdicH2DegreeEquiv K d ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ (graphOver d v hv) 2
          (M.nativeRationalDiagonalMiddleClass ℓ hℓ)) =
      (Nat.card {s : Spec (CommRingCat.of K) ⟶ C //
        s ≫ d = 𝟙 _ ∧ s ≫ v = s} : ℚ_[ℓ]) - 1 - (Fintype.card k : ℚ_[ℓ]) ^ m := by
  intro C d v hv hproper hsmooth algKC M
  let e := nativeRationalEllAdicH2DegreeEquiv K d ℓ hℓ
  let I := (graphOver d (𝟙 C) (Category.id_comp d)).ker.comap (graphOver d v hv)
  have hI : I.IsInvertible :=
    Scheme.constantBaseChangeFrobenius_componentFixedIdeal_isInvertible k K X m Z hZ
  have hcount : (M.cartierModulus I hI).degree =
      Nat.card {s : Spec (CommRingCat.of K) ⟶ C // s ≫ d = 𝟙 _ ∧ s ≫ v = s} :=
    Scheme.constantBaseChangeFrobenius_componentFixedCartierModulus_degree_pointCount
      k K X m Z hZ
  have ha : rationalEllAdicCohomologyPullback ℓ v 2 (e.symm 1) =
      (Fintype.card k ^ m) • e.symm 1 := by
    have h := LinearMap.congr_fun
      (nativeFrobeniusFixedComponentH2 k K X ℓ hℓ m Z hZ) (e.symm 1)
    simpa only [LinearMap.smul_apply, Module.End.one_apply] using h
  have h := M.nativeRationalDiagonalMiddleClass_graph_degree ℓ hℓ v hv hI
  change e (rationalEllAdicCohomologyPullback ℓ (graphOver d v hv) 2
      (M.nativeRationalDiagonalMiddleClass ℓ hℓ)) =
    ((M.cartierModulus I hI).degree : ℚ_[ℓ]) -
      e (rationalEllAdicCohomologyPullback ℓ v 2 (e.symm 1)) - 1 at h
  rw [hcount, Int.cast_natCast, ha, map_nsmul, LinearEquiv.apply_symm_apply,
    nsmul_eq_mul, mul_one, Nat.cast_pow] at h
  rw [h]
  ring

end AlgebraicGeometry.SmoothProperCurve
