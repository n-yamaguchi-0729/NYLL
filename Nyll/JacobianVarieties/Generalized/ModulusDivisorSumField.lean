/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.AlgebraicCurves.Models.Divisors.CartierRelativePointSums
import Nyll.JacobianVarieties.Generalized.ModulusCurveIdeal
import Nyll.JacobianVarieties.Generalized.ModulusEvaluation
import Nyll.JacobianVarieties.Albanese.DivisorSumEvaluation

/-! # Regular divisor sums and actual function-field evaluation

These formulas identify the regular sum with the evaluation of the full Cartier
divisor, including repetitions. The tuple hypotheses concern actual ideals and
are discharged by geometric splitting of supported divisors.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian JacobianVarieties.Albanese
open scoped BigOperators

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

omit [IsAlgClosed K] in
private theorem modulusCurveIdeal_eq_pointTuple {n : ℕ}
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K))))
    (p : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (hp : E.I = prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)) :
    modulusCurveIdeal E =
      (prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)).comap
        (inv (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K))))) :=
  (modulusCurveIdeal_eq_comap E).trans
    (congrArg (fun I : (pullback M.toBase (𝟙 (Spec (CommRingCat.of K)))).IdealSheafData =>
      I.comap (inv (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K)))))) hp)

omit [IsAlgClosed K] in
private theorem cartierModulus_congr (I J : M.C.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    M.cartierModulus I hI = M.cartierModulus J hJ := by
  subst J
  rfl

/-- The full divisor of an actual point family is its finite place sum. -/
theorem modulusCurveIdeal_pointTuple {n : ℕ}
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K))))
    (p : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (hp : E.I = prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)) :
    M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E) =
      ∑ i, Finsupp.single (M.pointEquivPlace (p i)) 1 := by
  have he := M.modulusCurveIdeal_eq_pointTuple E p hp
  have hI := he ▸ modulusCurveIdeal_isInvertible E
  exact (M.cartierModulus_congr _ _ (modulusCurveIdeal_isInvertible E) hI he).trans
    (M.cartierModulus_relativePointSum p hI)

/-- Evaluating the full Cartier divisor gives the sum of the values at its points. -/
theorem divisorEvaluation_pointTuple {A : Type w} [AddCommGroup A]
    (a : Place K F → A) {n : ℕ}
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K))))
    (p : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (hp : E.I = prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)) :
    Divisor.evaluation a
      (M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)).toDivisor =
        ∑ i, a (M.pointEquivPlace (p i)) := by
  classical
  let ev : Modulus K F →+ A :=
    { toFun := fun D => Divisor.evaluation a D.toDivisor
      map_zero' := by rw [Modulus.toDivisor_zero, map_zero]
      map_add' := fun D E => by rw [Modulus.toDivisor_add, map_add] }
  change ev (M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)) = _
  rw [M.modulusCurveIdeal_pointTuple E p hp, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change Divisor.evaluation a
    (Modulus.toDivisor (Finsupp.single (M.pointEquivPlace (p i)) 1)) = _
  rw [Modulus.toDivisor, Finsupp.mapRange_single, Nat.cast_one,
    Divisor.evaluation_single, one_zsmul]

/-- The actual supported regular sum agrees with full-divisor evaluation on a
tuple presentation. The evaluator may be any homomorphism out of the point group. -/
theorem value_supportedDivisorSum_pointTuple
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
    (E : RelEffCartierDiv M.toBase n (𝟙 (Spec (CommRingCat.of K)))) (hE : E.SupportedIn U)
    (xs : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase))
    (hfull : E.I = prodKerGraph M.toBase (fun i => (xs i).1 ≫ U.ι)
      (fun i => (Category.assoc _ _ _).trans (xs i).2))
    (hopen : (E.restrictToOpen M.toBase U hE).I =
      prodKerGraph (U.ι ≫ M.toBase) (fun i => (xs i).1) (fun i => (xs i).2)) :
    v (supportedDivisorSum M.toBase U hD sum E hE) =
      Divisor.evaluation a
        (M.cartierModulus (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)).toDivisor := by
  classical
  rw [supportedDivisorSum_evaluate_tuple M.toBase U hD σ hσ hI G q sum hsum
    (𝟙 _) xs E hE hopen, G.value_sumList (𝟙 _) v hv hm, List.map_ofFn, List.sum_ofFn]
  rw [M.divisorEvaluation_pointTuple a E
    (fun i => ⟨(xs i).1 ≫ U.ι, (Category.assoc _ _ _).trans (xs i).2⟩) hfull]
  apply Finset.sum_congr rfl
  intro i hi
  exact (ha (xs i)).symm

end AlgebraicCurve.CurveModel
