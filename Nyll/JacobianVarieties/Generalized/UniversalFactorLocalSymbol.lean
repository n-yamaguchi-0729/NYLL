/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusPointEvaluation
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.IsolatedLocalBoundary

/-! # Universal group factors and actual local-symbol values

The group morphism factoring a normalized curve map induces the original
divisor evaluator on every point of the generalized Jacobian. Its values on
the actual principal boundary are consequently the negative sum of local
symbols. Isolated full jets realize individual local symbols as such values.
These comparisons use a proved modulus; they do not assume or assert general
modulus existence.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (G : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)
  (hmod : M.regularMapHasModulus D G q)
  (hε : ε ≫ Over.homMk q.1 q.2 = 1)
  (φ : groupScheme M.toBase D ⟶ G)
  (hφ : modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom = Over.homMk q.1 q.2)

include hε hφ

/-- The actual universal group factor induces exactly the full-modulus
divisor evaluator, not merely its restriction to Abel points. -/
theorem groupFactor_pointEvaluation :
    (IsMonHom.monoidHom φ.hom.hom.hom
      (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive =
      M.modulusPointEvaluation D
        (M.regularMapValues (modulusComplement (modulusCurveMap D)) G q) hmod := by
  apply M.modulusAbel_points_addHom_ext D ε
  intro x
  rw [M.modulusPointEvaluation_abel D ε x
    (M.regularMapValues (modulusComplement (modulusCurveMap D)) G q) hmod]
  change Additive.ofMul ((x ≫ modulusAbelMap M.toBase D ε) ≫ φ.hom.hom.hom) =
    M.regularMapValues (modulusComplement (modulusCurveMap D)) G q
      (M.openPointPlace (modulusComplement (modulusCurveMap D)) ⟨x.left, Over.w x⟩) -
    M.regularMapValues (modulusComplement (modulusCurveMap D)) G q
      (M.openPointPlace (modulusComplement (modulusCurveMap D)) ⟨ε.left, Over.w ε⟩)
  rw [M.regularMapValues_apply, M.regularMapValues_apply]
  change Additive.ofMul ((x ≫ modulusAbelMap M.toBase D ε) ≫ φ.hom.hom.hom) =
    Additive.ofMul (x ≫ Over.homMk q.1 q.2) - Additive.ofMul (ε ≫ Over.homMk q.1 q.2)
  rw [Category.assoc, hφ, hε]
  exact (sub_zero _).symm

/-- The value of the actual group factor on the principal boundary is
the negative sum of the original local symbols, with its reciprocity sign. -/
theorem groupFactor_unitBoundary :
    let hc : IsCurveOver K F :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase M.ffEquiv M.ffEquiv_algebraMap
    let _ : HasPrincipalDivisors K F := hc.toHasPrincipalDivisors
    ∀ f : (M.functionFieldModulus D).awayUnits,
      Additive.ofMul ((M.divisorClassPointEquiv D
        ((M.functionFieldModulus D).unitBoundary (Additive.ofMul f))).toMul ≫
          φ.hom.hom.hom) =
        -∑ w ∈ (M.functionFieldModulus D).support,
          hmod.localSymbol w (Additive.ofMul f.1) := by
  intro hc principals f
  have he := DFunLike.congr_fun (M.groupFactor_pointEvaluation D ε G q hmod hε φ hφ)
    (M.divisorClassPointEquiv D
      ((M.functionFieldModulus D).unitBoundary (Additive.ofMul f)))
  change _ = hmod.classEvaluationZero
    ((M.divisorClassPointEquiv D).symm (M.divisorClassPointEquiv D _)) at he
  rw [AddEquiv.symm_apply_apply] at he
  exact he.trans (Modulus.HasModulus.classEvaluationZero_unitBoundary_eq_neg_sum
    (D := M.functionFieldModulus D) hmod f)

/-- Every unit jet at a modulus place is realized by a principal boundary
whose image under the actual group factor is minus the given local symbol.
The other full jets are one; no isolated representative is assumed. -/
theorem groupFactor_exists_isolated_boundary :
    let hc : IsCurveOver K F :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase M.ffEquiv M.ffEquiv_algebraMap
    let _ : HasPrincipalDivisors K F := hc.toHasPrincipalDivisors
    ∀ (w : Place K F), M.functionFieldModulus D w ≠ 0 →
      ∀ (g : Fˣ), w.ord (g : F) = 0 →
        ∃ f : (M.functionFieldModulus D).awayUnits,
          w.CongruentOne (M.functionFieldModulus D w) ((f.1 / g : Fˣ) : F) ∧
          (∀ z : Place K F, M.functionFieldModulus D z ≠ 0 → z ≠ w →
            z.CongruentOne (M.functionFieldModulus D z) (f.1 : F)) ∧
          Additive.ofMul ((M.divisorClassPointEquiv D
            ((M.functionFieldModulus D).unitBoundary (Additive.ofMul f))).toMul ≫
              φ.hom.hom.hom) = -hmod.localSymbol w (Additive.ofMul g) := by
  intro hc principals w hw g hg
  obtain ⟨f, hf, hother, he⟩ := hmod.exists_isolated_unitBoundary w hw g hg
  refine ⟨f, hf, hother, ?_⟩
  have heval := DFunLike.congr_fun (M.groupFactor_pointEvaluation D ε G q hmod hε φ hφ)
    (M.divisorClassPointEquiv D
      ((M.functionFieldModulus D).unitBoundary (Additive.ofMul f)))
  change _ = hmod.classEvaluationZero
    ((M.divisorClassPointEquiv D).symm (M.divisorClassPointEquiv D _)) at heval
  rw [AddEquiv.symm_apply_apply] at heval
  exact heval.trans he

end AlgebraicCurve.CurveModel
