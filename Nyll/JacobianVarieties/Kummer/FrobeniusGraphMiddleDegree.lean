/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Divisors.FrobeniusFixedCartierDegree
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.GraphAdicCycleClass
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalGraphEdges
public import Nyll.EtaleCohomology.Classical.RationalKunnethEdgeSplitting
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalEdgeClass
public import Nyll.JacobianVarieties.Kummer.FrobeniusGraphCycleDegree
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2Frobenius
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Actual Frobenius-graph degree of the normalized diagonal

The original two native degree-one edge classes contribute q^m and one
under original Frobenius-graph pullback. The actual full diagonal already
has degree equal to the original finite-extension point count. The same
original normalized diagonal therefore has graph-pullback degree
point count minus one minus q^m.

The remaining identification of this actual middle degree with minus
the original H¹ trace is not assumed or asserted here.
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
local notation "v" => End.asHom ((End.of (Scheme.constantBaseChangeFrobenius k K X)) ^ m)
local notation "Γ" => graphOver g v (Scheme.constantBaseChangeFrobenius_pow_snd k K X m)
local notation "N" => Nat.card (SchemeHomOver
  (Spec.algebraMap k (LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m))
  (X ↘ Spec (CommRingCat.of k)))

include hℓ in
omit [NeZero m] in
private theorem rationalH2_actualFrobeniusPower
    (a : rationalEllAdicCohomology ℓ Y 2) :
    rationalEllAdicCohomologyPullback ℓ v 2 a = (Fintype.card k ^ m) • a := by
  have h := LinearMap.congr_fun
    (rationalEllAdicH2_geometricFrobenius_pow k K X ℓ hℓ m) a
  rw [finiteFieldFrobeniusRationalEllAdicCohomology_pow k K X ℓ 2 m] at h
  simpa only [LinearMap.smul_apply, Module.End.one_apply] using h

omit [NeZero m] in
/-- The original Frobenius graph gives precisely q^m plus one on
the two actual native degree-one edge classes. -/
theorem rationalDiagonalEdges_frobeniusGraph_degree :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let e := SmoothProperCurve.nativeRationalEllAdicH2DegreeEquiv K g ℓ hℓ
    e (rationalEllAdicCohomologyPullback ℓ Γ 2
      (rationalEllAdicEdgeMap ℓ g g 2 (e.symm 1, e.symm 1))) =
      (Fintype.card k : ℚ_[ℓ]) ^ m + 1 := by
  intro hY e
  rw [rationalEllAdicEdgeMap_graphOver,
    rationalH2_actualFrobeniusPower k K X ℓ hℓ m,
    map_add, map_nsmul, LinearEquiv.apply_symm_apply,
    nsmul_eq_mul, mul_one, Nat.cast_pow]

/-- The original normalized diagonal has actual Frobenius-graph
degree equal to the actual point count minus its two proven edge terms. -/
theorem nativeRationalDiagonalMiddleClass_frobeniusGraph_degree :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : Algebra K (Scheme.functionField Y) :=
      (AlgebraicCurve.baseToFunctionField g).toAlgebra
    let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve g
    SmoothProperCurve.nativeRationalEllAdicH2DegreeEquiv K g ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ Γ 2
          (M.nativeRationalDiagonalMiddleClass ℓ hℓ)) =
      (N : ℚ_[ℓ]) - 1 - (Fintype.card k : ℚ_[ℓ]) ^ m := by
  intro hY algKY M
  let e := SmoothProperCurve.nativeRationalEllAdicH2DegreeEquiv K g ℓ hℓ
  have hP : IsIntegral (pullback g g) :=
    Scheme.constantBaseChange_smoothProperCurve_selfProduct_isIntegral k K X
  have hcount : e (rationalEllAdicCohomologyPullback ℓ Γ 2
      (rationalGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ)) =
      (N : ℚ_[ℓ]) := rationalDiagonalCycleClass_frobeniusGraph_degree k K X ℓ hℓ m
  have hedge : e (rationalEllAdicCohomologyPullback ℓ Γ 2
      (rationalEllAdicEdgeMap ℓ g g 2 (e.symm 1, e.symm 1))) =
      (Fintype.card k : ℚ_[ℓ]) ^ m + 1 :=
    rationalDiagonalEdges_frobeniusGraph_degree k K X ℓ hℓ m
  change e (rationalEllAdicCohomologyPullback ℓ Γ 2
      (rationalGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ -
        rationalEllAdicEdgeMap ℓ g g 2 (e.symm 1, e.symm 1))) = _
  rw [map_sub, map_sub, hcount, hedge,
    add_comm ((Fintype.card k : ℚ_[ℓ]) ^ m) 1, sub_add_eq_sub_sub]

end EtaleCohomology
