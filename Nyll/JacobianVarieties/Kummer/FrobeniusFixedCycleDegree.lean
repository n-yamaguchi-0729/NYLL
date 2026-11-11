/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Divisors.FrobeniusFixedCartierDegree
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.JacobianVarieties.Kummer.CurveCartierCycleDegree
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2
public import Mathlib.Data.Int.Cast.Basic

/-!
# The original Frobenius fixed cycle has the actual point-count degree

On the literal geometric curve, the native degree of the actual fixed
Cartier cycle class is the number of rational points over the original
finite extension. The finite, integral, and rational statements use the
same full graph-diagonal ideal and the same original cohomology groups.

This uses the proved Cartier-class degree calculation and the proved
comparison of the original relative degree with the original place
degree. It does not assume an intersection-to-cohomology comparison or
replace the fixed scheme by a chosen divisor of equal degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits NeronModelInfra
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
  (m : ℕ) [NeZero m]

local notation "Y" => pullback (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "g" => pullback.snd (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "D" => Scheme.constantBaseChangeFrobeniusFixedCartierDivisor k K X m
local notation "N" => Nat.card (SchemeHomOver
  (Spec.algebraMap k (LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m))
  (X ↘ Spec (CommRingCat.of k)))

/-- The actual fixed cycle's original finite H² degree is the actual
finite-extension point count in the original residue coefficient ring. -/
theorem finiteFrobeniusFixedCycleClass_degree (n : ℕ) :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    SmoothProperCurve.nativeFiniteLevelH2DegreeEquiv K g ℓ hℓ n
        (finiteEffectiveCartierCycleClass g ℓ hℓ n D) =
      (N : ZMod (ℓ ^ (n + 1))) := by
  intro hY
  let : Algebra K (Scheme.functionField Y) :=
    (AlgebraicCurve.baseToFunctionField g).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve g
  have hdegree :=
    Scheme.constantBaseChangeFrobenius_fixedCartierModulus_degree_pointCount k K X m
  change (M.cartierModulus D.1
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m)).degree =
      (N : ℤ) at hdegree
  have h := M.nativeFiniteLevelH2DegreeEquiv_cartier ℓ hℓ n D.1
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m)
  rw [hdegree, Int.cast_natCast] at h
  exact h

/-- The actual compatible fixed cycle has the actual point-count
degree in the original adic integers. -/
theorem integralFrobeniusFixedCycleClass_degree :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    SmoothProperCurve.nativeEllAdicH2DegreeEquiv K g ℓ hℓ
        (integralEffectiveCartierCycleClass g ℓ hℓ D) =
      (N : ℤ_[ℓ]) := by
  intro hY
  let : Algebra K (Scheme.functionField Y) :=
    (AlgebraicCurve.baseToFunctionField g).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve g
  have hdegree :=
    Scheme.constantBaseChangeFrobenius_fixedCartierModulus_degree_pointCount k K X m
  change (M.cartierModulus D.1
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m)).degree =
      (N : ℤ) at hdegree
  have h := M.nativeEllAdicH2DegreeEquiv_cartier ℓ hℓ D.1
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m)
  rw [hdegree, Int.cast_natCast] at h
  exact h

/-- The original rational H² degree of the actual Frobenius fixed
cycle is the number of points over the original degree-m extension. -/
theorem rationalFrobeniusFixedCycleClass_degree :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    SmoothProperCurve.nativeRationalEllAdicH2DegreeEquiv K g ℓ hℓ
        (rationalEffectiveCartierCycleClass g ℓ hℓ D) =
      (N : ℚ_[ℓ]) := by
  intro hY
  let : Algebra K (Scheme.functionField Y) :=
    (AlgebraicCurve.baseToFunctionField g).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve g
  have hdegree :=
    Scheme.constantBaseChangeFrobenius_fixedCartierModulus_degree_pointCount k K X m
  change (M.cartierModulus D.1
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m)).degree =
      (N : ℤ) at hdegree
  have h := M.nativeRationalEllAdicH2DegreeEquiv_cartier ℓ hℓ D.1
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m)
  rw [hdegree, Int.cast_natCast] at h
  exact h

end EtaleCohomology
