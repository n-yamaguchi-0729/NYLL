/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.CorrectedDivisorSumField
import Nyll.JacobianVarieties.Generalized.ModulusDivisorEvaluationInvariance
import Nyll.JacobianVarieties.Generalized.ModulusDivisorDifferenceClass
import Nyll.JacobianVarieties.Generalized.PicardZeroGeometricEquality
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ExtCompEq

/-! # Corrected divisor sums agree on reduced overlaps

The equality assumed on the overlap is equality of actual zero-sheaf classes.
It is converted to equality of raw rigidifications only on field-valued points.
The full modulus-principal kernel then proves equality of the regular maps.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian JacobianVarieties.Albanese

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))

local notation "U" => modulusComplement (modulusCurveMap D)

/-- Actual corrected sum maps glue across reduced finite-type overlaps when their
zero-sheaf classes agree. The evaluator and its full modulus condition are explicit. -/
theorem correctedSupportedDivisorSum_eq_of_zeroSheafClass
    {B Y₀ Y₁ T : Scheme.{u}} {n₀ n₁ rP : ℕ}
    {y₀ : Y₀ ⟶ Spec (CommRingCat.of K)} {y₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {D₀ : RelEffCartierDiv ((U).ι ≫ M.toBase) n₀ y₀}
    {D₁ : RelEffCartierDiv ((U).ι ≫ M.toBase) n₁ y₁}
    (hD₀ : D₀.IsUniversal) (σ₀ : finFibrePow ((U).ι ≫ M.toBase) n₀ ⟶ Y₀)
    (hσ₀ : σ₀ ≫ y₀ = finFibrePow.toBase ((U).ι ≫ M.toBase) n₀)
    (hI₀ : D₀.I.comap (mapOnProdOver ((U).ι ≫ M.toBase) σ₀ hσ₀) =
      fibrePowOver.tautIdeal ((U).ι ≫ M.toBase) n₀)
    (hD₁ : D₁.IsUniversal) (σ₁ : finFibrePow ((U).ι ≫ M.toBase) n₁ ⟶ Y₁)
    (hσ₁ : σ₁ ≫ y₁ = finFibrePow.toBase ((U).ι ≫ M.toBase) n₁)
    (hI₁ : D₁.I.comap (mapOnProdOver ((U).ι ≫ M.toBase) σ₁ hσ₁) =
      fibrePowOver.tautIdeal ((U).ι ≫ M.toBase) n₁)
    {b : B ⟶ Spec (CommRingCat.of K)} [IsSeparated b] (G : RelativeGroupLaw K b)
    (q : SchemeHomOver ((U).ι ≫ M.toBase) b)
    (sum₀ : SchemeHomOver y₀ b) (sum₁ : SchemeHomOver y₁ b)
    (hsum₀ : σ₀ ≫ sum₀.1 = (G.finiteSumMap ((U).ι ≫ M.toBase) q n₀).1)
    (hsum₁ : σ₁ ≫ sum₁.1 = (G.finiteSumMap ((U).ι ≫ M.toBase) q n₁).1)
    (qε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b)
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
    (P : RelEffCartierDiv M.toBase rP (𝟙 (Spec (CommRingCat.of K)))) (hP : P.SupportedIn U)
    (hPvalue : Divisor.evaluation a
      (M.cartierModulus (modulusCurveIdeal P) (modulusCurveIdeal_isInvertible P)).toDivisor = v qε)
    (t : T ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType t] [IsReduced T]
    (E₀ : RelEffCartierDiv M.toBase n₀ t) (hE₀ : E₀.SupportedIn U)
    (E₁ : RelEffCartierDiv M.toBase n₁ t) (hE₁ : E₁.SupportedIn U) :
    let Q := P.pullbackAlong t (Category.comp_id t)
    let hQ := hP.pullbackAlong t (Category.comp_id t)
    let z₀ := modulusDivisorDifferenceClass M.toBase (modulusCurveMap D) E₀ hE₀ Q hQ n₀
    let z₁ := modulusDivisorDifferenceClass M.toBase (modulusCurveMap D) E₁ hE₁ Q hQ n₁
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
      correctedSupportedDivisorSum M.toBase U hD₀ G sum₀ qε E₀ hE₀ =
        correctedSupportedDivisorSum M.toBase U hD₁ G sum₁ qε E₁ hE₁ := by
  intro Q hQ z₀ z₁ hz₀ hz₁ hη
  apply Subtype.ext
  apply ext_of_forall_comp_eq_of_isAlgClosed t b
    (correctedSupportedDivisorSum M.toBase U hD₀ G sum₀ qε E₀ hE₀).property
    (correctedSupportedDivisorSum M.toBase U hD₁ G sum₁ qε E₁ hE₁).property
  intro p hp
  have hraw := modulusPicardZero_raw_eq_on_geometricPoint M.toBase (modulusCurveMap D)
    (T := Over.mk t) ⟨z₀, hz₀⟩ ⟨z₁, hz₁⟩ hη
    (s := 𝟙 (Spec (CommRingCat.of K))) (Over.homMk p hp)
  change (modulusPicardGroupPresheaf M.toBase (modulusCurveMap D)).map
      (Over.homMk p hp : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk t).op
      (modulusDivisorDifferenceClass M.toBase (modulusCurveMap D) E₀ hE₀ Q hQ n₀) =
    (modulusPicardGroupPresheaf M.toBase (modulusCurveMap D)).map
      (Over.homMk p hp : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk t).op
      (modulusDivisorDifferenceClass M.toBase (modulusCurveMap D) E₁ hE₁ Q hQ n₁) at hraw
  rw [modulusDivisorDifferenceClass_naturality,
    modulusDivisorDifferenceClass_naturality] at hraw
  change modulusDivisorDifferenceClass M.toBase (modulusCurveMap D)
      (E₀.pullbackAlong p hp) (hE₀.pullbackAlong p hp)
      (Q.pullbackAlong p hp) (hQ.pullbackAlong p hp) n₀ =
    modulusDivisorDifferenceClass M.toBase (modulusCurveMap D)
      (E₁.pullbackAlong p hp) (hE₁.pullbackAlong p hp)
      (Q.pullbackAlong p hp) (hQ.pullbackAlong p hp) n₁ at hraw
  have hQp : Q.pullbackAlong p hp = P := by
    change (P.pullbackAlong t (Category.comp_id t)).pullbackAlong p hp = P
    rw [RelEffCartierDiv.pullbackAlong_comp]
    have hbase : ∀ (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
        (hf : f ≫ 𝟙 (Spec (CommRingCat.of K)) = 𝟙 _),
        f = 𝟙 _ → P.pullbackAlong f hf = P := by
      intro f hf he
      subst f
      exact P.pullbackAlong_id
    exact hbase _ _ hp
  have hclasses :
      modulusDivisorFamilyClass M.toBase (modulusCurveMap D)
          (E₀.pullbackAlong p hp) (hE₀.pullbackAlong p hp) /
        modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n₀ =
      modulusDivisorFamilyClass M.toBase (modulusCurveMap D)
          (E₁.pullbackAlong p hp) (hE₁.pullbackAlong p hp) /
        modulusDivisorFamilyClass M.toBase (modulusCurveMap D) P hP ^ n₁ := by
    simpa only [hQp, modulusDivisorDifferenceClass] using hraw
  have heval := M.divisorEvaluation_sub_nsmul_eq_of_familyClass_div_pow_eq D a hmod
    (E₀.pullbackAlong p hp) (hE₀.pullbackAlong p hp)
    (E₁.pullbackAlong p hp) (hE₁.pullbackAlong p hp) P hP n₀ n₁ hclasses
  have heq :
      correctedSupportedDivisorSum M.toBase U hD₀ G sum₀ qε
        (E₀.pullbackAlong p hp) (hE₀.pullbackAlong p hp) =
      correctedSupportedDivisorSum M.toBase U hD₁ G sum₁ qε
        (E₁.pullbackAlong p hp) (hE₁.pullbackAlong p hp) := by
    apply hv
    rw [M.value_correctedSupportedDivisorSum_field U hD₀ σ₀ hσ₀ hI₀ G q sum₀ hsum₀
      qε v hv₁ hv₂ a ha, M.value_correctedSupportedDivisorSum_field U hD₁ σ₁ hσ₁ hI₁ G q
      sum₁ hsum₁ qε v hv₁ hv₂ a ha, ← hPvalue]
    exact heval
  have hn₀ := correctedSupportedDivisorSum_naturality M.toBase U hD₀ G sum₀ qε E₀ hE₀ p hp
  have hn₁ := correctedSupportedDivisorSum_naturality M.toBase U hD₁ G sum₁ qε E₁ hE₁ p hp
  exact (congrArg Subtype.val hn₀).trans
    ((congrArg Subtype.val heq).trans (congrArg Subtype.val hn₁).symm)

end AlgebraicCurve.CurveModel
