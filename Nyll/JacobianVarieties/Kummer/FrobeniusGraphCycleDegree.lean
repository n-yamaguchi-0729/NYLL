/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.FrobeniusFixedCartierDegree
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCyclePullback
public import Nyll.EtaleCohomology.Classical.GraphAdicCycleClass
public import Nyll.JacobianVarieties.Kummer.FrobeniusFixedCycleDegree
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2

/-!
# Actual Frobenius graph pullback of the diagonal cycle

The original diagonal Cartier cycle on the literal geometric product
pulls back along the original Frobenius graph to the original fixed
Cartier cycle. The equality uses the full inverse-image ideal and the
proved Cartier pullback theorem, including its actual Kummer boundaries.
Its native degree is therefore the actual finite-extension point count.

The finite, integral, and rational statements use the original
cohomology pullbacks and the same actual diagonal and graph. No
intersection-to-cohomology comparison is supplied as a hypothesis.
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
local notation "D" => Scheme.constantBaseChangeFrobeniusFixedCartierDivisor k K X m
local notation "N" => Nat.card (SchemeHomOver
  (Spec.algebraMap k (LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m))
  (X ↘ Spec (CommRingCat.of k)))

omit [IsAlgClosed K] [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))] [NeZero m] in
private theorem frobeniusGraph_productStructure :
    Γ ≫ (pullback.snd g g ≫ g) = g := by
  rw [← Category.assoc, graphOver_snd, Category.id_comp]

/-- The original finite diagonal class pulls back to the actual fixed
cycle, with the same entire graph-diagonal ideal. -/
theorem finiteDiagonalCycleClass_frobeniusGraph_pullback (n : ℕ) :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : IsIntegral (pullback g g) :=
      Scheme.constantBaseChange_smoothProperCurve_selfProduct_isIntegral k K X
    finiteLevelCohomologyPullback ℓ Γ n 2
        (finiteGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ n) =
      finiteEffectiveCartierCycleClass g ℓ hℓ n D := by
  intro hY hP
  have hD : ((graphEffectiveCartierDivisor g g (𝟙 Y) (Category.id_comp g)).1.comap
      Γ).IsEffectiveCartier :=
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m).isEffectiveCartier
  have h := finiteEffectiveCartierCycleClass_pullback Γ (pullback.snd g g ≫ g)
    ℓ hℓ n (graphEffectiveCartierDivisor g g (𝟙 Y) (Category.id_comp g)) hD
  rw [frobeniusGraph_productStructure k K X m] at h
  exact h

/-- The original compatible diagonal family pulls back to the
compatible fixed cycle in actual integral cohomology. -/
theorem integralDiagonalCycleClass_frobeniusGraph_pullback :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : IsIntegral (pullback g g) :=
      Scheme.constantBaseChange_smoothProperCurve_selfProduct_isIntegral k K X
    ellAdicCohomologyPullback ℓ Γ 2
        (integralGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ) =
      integralEffectiveCartierCycleClass g ℓ hℓ D := by
  intro hY hP
  have hD : ((graphEffectiveCartierDivisor g g (𝟙 Y) (Category.id_comp g)).1.comap
      Γ).IsEffectiveCartier :=
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m).isEffectiveCartier
  have h := integralEffectiveCartierCycleClass_pullback Γ (pullback.snd g g ≫ g)
    ℓ hℓ (graphEffectiveCartierDivisor g g (𝟙 Y) (Category.id_comp g)) hD
  rw [frobeniusGraph_productStructure k K X m] at h
  exact h

/-- The original rational diagonal class pulls back along the actual
Frobenius graph to the original rational fixed cycle. -/
theorem rationalDiagonalCycleClass_frobeniusGraph_pullback :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : IsIntegral (pullback g g) :=
      Scheme.constantBaseChange_smoothProperCurve_selfProduct_isIntegral k K X
    rationalEllAdicCohomologyPullback ℓ Γ 2
        (rationalGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ) =
      rationalEffectiveCartierCycleClass g ℓ hℓ D := by
  intro hY hP
  have hD : ((graphEffectiveCartierDivisor g g (𝟙 Y) (Category.id_comp g)).1.comap
      Γ).IsEffectiveCartier :=
    (Scheme.constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m).isEffectiveCartier
  have h := rationalEffectiveCartierCycleClass_pullback Γ (pullback.snd g g ≫ g)
    ℓ hℓ (graphEffectiveCartierDivisor g g (𝟙 Y) (Category.id_comp g)) hD
  rw [frobeniusGraph_productStructure k K X m] at h
  exact h

/-- Finite coefficient degree of the actual graph pullback of the
actual diagonal is the original finite-extension point count. -/
theorem finiteDiagonalCycleClass_frobeniusGraph_degree (n : ℕ) :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : IsIntegral (pullback g g) :=
      Scheme.constantBaseChange_smoothProperCurve_selfProduct_isIntegral k K X
    SmoothProperCurve.nativeFiniteLevelH2DegreeEquiv K g ℓ hℓ n
        (finiteLevelCohomologyPullback ℓ Γ n 2
          (finiteGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ n)) =
      (N : ZMod (ℓ ^ (n + 1))) := by
  intro hY hP
  rw [finiteDiagonalCycleClass_frobeniusGraph_pullback k K X ℓ hℓ m n]
  exact finiteFrobeniusFixedCycleClass_degree k K X ℓ hℓ m n

/-- The native integral degree of the actual graph-diagonal
intersection class is the actual number of finite-extension points. -/
theorem integralDiagonalCycleClass_frobeniusGraph_degree :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : IsIntegral (pullback g g) :=
      Scheme.constantBaseChange_smoothProperCurve_selfProduct_isIntegral k K X
    SmoothProperCurve.nativeEllAdicH2DegreeEquiv K g ℓ hℓ
        (ellAdicCohomologyPullback ℓ Γ 2
          (integralGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ)) =
      (N : ℤ_[ℓ]) := by
  intro hY hP
  rw [integralDiagonalCycleClass_frobeniusGraph_pullback k K X ℓ hℓ m]
  exact integralFrobeniusFixedCycleClass_degree k K X ℓ hℓ m

/-- The original rational degree of Frobenius-graph pullback of the
actual diagonal cycle equals the actual degree-m point count. -/
theorem rationalDiagonalCycleClass_frobeniusGraph_degree :
    let _ : IsIntegral Y := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : IsIntegral (pullback g g) :=
      Scheme.constantBaseChange_smoothProperCurve_selfProduct_isIntegral k K X
    SmoothProperCurve.nativeRationalEllAdicH2DegreeEquiv K g ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ Γ 2
          (rationalGraphCycleClass g g (𝟙 Y) (Category.id_comp g) ℓ hℓ)) =
      (N : ℚ_[ℓ]) := by
  intro hY hP
  rw [rationalDiagonalCycleClass_frobeniusGraph_pullback k K X ℓ hℓ m]
  exact rationalFrobeniusFixedCycleClass_degree k K X ℓ hℓ m

end EtaleCohomology
