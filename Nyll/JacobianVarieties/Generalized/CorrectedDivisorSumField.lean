/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorSumFieldActual
import Nyll.JacobianVarieties.Albanese.CorrectedDivisorSums
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedInOfPoint

/-! # Full-divisor evaluation of corrected regular sums -/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian JacobianVarieties.Albanese

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- A genuine basepoint divisor evaluates to the value of that basepoint. -/
theorem divisorEvaluation_ofPoint {A : Type w} [AddCommGroup A]
    (a : Place K F → A)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal (RelEffCartierDiv.ofPoint M.toBase ε.1 ε.2))
          (modulusCurveIdeal_isInvertible _)).toDivisor = a (M.pointEquivPlace ε) := by
  have hI : (RelEffCartierDiv.ofPoint M.toBase ε.1 ε.2).I =
      prodKerGraph M.toBase (fun _ : Fin 1 => ε.1) (fun _ => ε.2) := by
    rw [RelEffCartierDiv.ofPoint_I, prodKerGraph_one]
  rw [M.divisorEvaluation_pointTuple a (RelEffCartierDiv.ofPoint M.toBase ε.1 ε.2)
    (fun _ : Fin 1 => ε) hI, Fin.sum_univ_one]

/-- The correction in the actual regular map equals subtraction in full Cartier evaluation. -/
theorem value_correctedSupportedDivisorSum_field
    {B Y : Scheme.{u}} (U : M.C.Opens) {n : ℕ}
    {y : Y ⟶ Spec (CommRingCat.of K)} {D : RelEffCartierDiv (U.ι ≫ M.toBase) n y}
    (hD : D.IsUniversal) (σ : finFibrePow (U.ι ≫ M.toBase) n ⟶ Y)
    (hσ : σ ≫ y = finFibrePow.toBase (U.ι ≫ M.toBase) n)
    (hI : D.I.comap (mapOnProdOver (U.ι ≫ M.toBase) σ hσ) =
      fibrePowOver.tautIdeal (U.ι ≫ M.toBase) n)
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver (U.ι ≫ M.toBase) b) (sum : SchemeHomOver y b)
    (hsum : σ ≫ sum.1 = (G.finiteSumMap (U.ι ≫ M.toBase) q n).1)
    (qε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b)
    {A : Type w} [AddCommGroup A]
    (v : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b → A)
    (hv : v (G.one (𝟙 _)) = 0)
    (hm : ∀ x y, v (G.mul (𝟙 _) x y) = v x + v y)
    (a : Place K F → A)
    (ha : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase),
      a (M.pointEquivPlace ⟨x.1 ≫ U.ι, (Category.assoc _ _ _).trans x.2⟩) =
        v (NeronModelInfra.schemeHomOverComp x q))
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K)))) (hE : E.SupportedIn U) :
    v (correctedSupportedDivisorSum M.toBase U hD G sum qε E hE) =
      Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)).toDivisor -
          n • v qε := by
  rw [value_correctedSupportedDivisorSum M.toBase U hD G sum qε E hE v hv hm,
    M.value_supportedDivisorSum U hD σ hσ hI G q sum hsum v hv hm a ha E hE]
  have he : GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of K)))
      (Category.comp_id _) qε = qε := Subtype.ext (Category.id_comp qε.1)
  rw [he]

end AlgebraicCurve.CurveModel
