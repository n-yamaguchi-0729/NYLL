/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorSumField
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedDivisorGeometricTuples

/-! # Full Cartier evaluation of an arbitrary supported divisor sum -/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian JacobianVarieties.Albanese

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- The actual regular sum of every supported divisor evaluates its full Cartier divisor. -/
theorem value_supportedDivisorSum
    {B Y : Scheme.{u}} (U : M.C.Opens) {n : ℕ}
    {y : Y ⟶ Spec (CommRingCat.of K)} {D : RelEffCartierDiv (U.ι ≫ M.toBase) n y}
    (hD : D.IsUniversal) (σ : finFibrePow (U.ι ≫ M.toBase) n ⟶ Y)
    (hσ : σ ≫ y = finFibrePow.toBase (U.ι ≫ M.toBase) n)
    (hI : D.I.comap (mapOnProdOver (U.ι ≫ M.toBase) σ hσ) =
      fibrePowOver.tautIdeal (U.ι ≫ M.toBase) n)
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver (U.ι ≫ M.toBase) b) (sum : SchemeHomOver y b)
    (hsum : σ ≫ sum.1 = (G.finiteSumMap (U.ι ≫ M.toBase) q n).1)
    {A : Type w} [AddCommGroup A]
    (v : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b → A)
    (hv : v (G.one (𝟙 _)) = 0)
    (hm : ∀ x y, v (G.mul (𝟙 _) x y) = v x + v y)
    (a : Place K F → A)
    (ha : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase),
      a (M.pointEquivPlace ⟨x.1 ≫ U.ι, (Category.assoc _ _ _).trans x.2⟩) =
        v (NeronModelInfra.schemeHomOverComp x q))
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K)))) (hE : E.SupportedIn U) :
    v (supportedDivisorSum M.toBase U hD sum E hE) =
      Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)).toDivisor := by
  obtain ⟨xs, hfull, hopen⟩ :=
    RelEffCartierDiv.exists_supported_geometric_tuple M.toBase U E hE
  exact M.value_supportedDivisorSum_pointTuple U hD σ hσ hI G q sum hsum
    v hv hm a ha E hE xs hfull hopen

end AlgebraicCurve.CurveModel
