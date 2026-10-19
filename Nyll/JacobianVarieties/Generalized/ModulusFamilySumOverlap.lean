/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.JacobianVarieties.Generalized.CorrectedDivisorSumOverlap
import Nyll.JacobianVarieties.Generalized.ModulusBasepointDivisorClass

/-! # The constructed local sums respect the actual corrected zero-sheaf class -/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian JacobianVarieties.Albanese

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))

local notation "U" => modulusComplement (modulusCurveMap D)

/-- The explicitly constructed family sums agree whenever their corrected zero-sheaf classes do. -/
theorem modulusFamilySum_eq_of_zeroSheafClass
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) ((U).ι ≫ M.toBase))
    {B T : Scheme.{u}} {b : B ⟶ Spec (CommRingCat.of K)} [IsSeparated b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative) (q : SchemeHomOver ((U).ι ≫ M.toBase) b)
    {A : Type w} [AddCommGroup A]
    (v : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b → A) (hv : Function.Injective v)
    (hv₁ : v (G.one (𝟙 _)) = 0)
    (hv₂ : ∀ x y, v (G.mul (𝟙 _) x y) = v x + v y)
    (a : Place K F → A)
    (ha : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) ((U).ι ≫ M.toBase),
      a (M.pointEquivPlace ⟨x.1 ≫ (U).ι, (Category.assoc _ _ _).trans x.2⟩) =
        v (NeronModelInfra.schemeHomOverComp x q))
    (hmod : (M.cartierModulus (modulusCurveIdeal D)
      (modulusCurveIdeal_isInvertible D)).HasModulus a)
    (t : T ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType t] [IsReduced T] {n₀ n₁ : ℕ}
    (E₀ : RelEffCartierDiv M.toBase n₀ t) (hE₀ : E₀.SupportedIn U)
    (E₁ : RelEffCartierDiv M.toBase n₁ t) (hE₁ : E₁.SupportedIn U) :
    let e := RigidifiedLineBundle.classOf (modulusCanonicalPointBundle M.toBase (modulusCurveMap D)
      (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) ε))
    let z₀ := modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E₀ hE₀ / e ^ n₀
    let z₁ := modulusDivisorFamilyClass M.toBase (modulusCurveMap D) E₁ hE₁ / e ^ n₁
    ∀ (hz₀ : z₀ ∈ (modulusPicardZeroSubfunctor M.toBase (modulusCurveMap D)).obj
        (op (Over.mk t)))
      (hz₁ : z₁ ∈ (modulusPicardZeroSubfunctor M.toBase (modulusCurveMap D)).obj
        (op (Over.mk t))),
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf M.toBase (modulusCurveMap D))).app
          (op (Over.mk t)) ⟨z₀, hz₀⟩ =
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf M.toBase (modulusCurveMap D))).app
          (op (Over.mk t)) ⟨z₁, hz₁⟩ →
      modulusFamilySum M.toBase D ε G hc q E₀ hE₀ =
        modulusFamilySum M.toBase D ε G hc q E₁ hE₁ := by
  intro e z₀ z₁ hz₀ hz₁ hη
  let S₀ := chooseOpenCurveSum M.toBase U G q n₀ hc ε
  let S₁ := chooseOpenCurveSum M.toBase U G q n₁ hc ε
  let P := RelEffCartierDiv.ofPoint M.toBase (ε.1 ≫ (U).ι) ((Category.assoc _ _ _).trans ε.2)
  have hP : P.SupportedIn U := RelEffCartierDiv.supportedIn_ofPoint
    (f := M.toBase) (ε.1 ≫ (U).ι) ((Category.assoc _ _ _).trans ε.2) U
    (fun z => (ε.1 z).property)
  have hPvalue : Divisor.evaluation a
      (M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor =
      v (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q) :=
    (M.divisorEvaluation_ofPoint a ⟨ε.1 ≫ (U).ι, (Category.assoc _ _ _).trans ε.2⟩).trans (ha ε)
  have H := M.correctedSupportedDivisorSum_eq_of_zeroSheafClass D
    S₀.universal S₀.tupleMap S₀.tupleMap_toBase S₀.tuple_ideal
    S₁.universal S₁.tupleMap S₁.tupleMap_toBase S₁.tuple_ideal
    G q S₀.sum S₁.sum S₀.tuple_sum S₁.tuple_sum
    (GoodReductionJacobian.schemeHomOverComp ε.1 ε.2 q)
    v hv hv₁ hv₂ a ha hmod P hP hPvalue t E₀ hE₀ E₁ hE₁
  dsimp only at H
  have he : modulusDivisorFamilyClass M.toBase (modulusCurveMap D)
      (P.pullbackAlong t (Category.comp_id t)) (hP.pullbackAlong t (Category.comp_id t)) = e :=
    modulusDivisorFamilyClass_basepoint_pullback M.toBase (modulusCurveMap D) ε t
  simp only [modulusDivisorDifferenceClass, he] at H
  exact H hz₀ hz₁ hη

end AlgebraicCurve.CurveModel
