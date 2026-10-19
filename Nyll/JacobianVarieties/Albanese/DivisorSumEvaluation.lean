/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.SupportedDivisorSums
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.IEqProdKerGraphAlgClosed

/-! # Evaluating the regular sum of an actual divisor family

The tuple-cover formula determines the sum on every divisor which is a sum of
sections. It holds over arbitrary test schemes, including nonreduced schemes.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open AlgebraicCurves.RelativeDivisors.Proofs
open RelEffCartierDiv_IsUniversal_exists_sumMap.AlgebraicGeometry

namespace JacobianVarieties.Albanese

/-- The actual regular divisor sum evaluates a sum of sections to the sum of
their images. The ideal equality retains all multiplicities. -/
theorem divisorSum_evaluate_tuple
    {K : Type u} [Field K] {C B Y T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c] {n : ℕ}
    {y : Y ⟶ Spec (CommRingCat.of K)} {E : RelEffCartierDiv c n y}
    (hE : E.IsUniversal) (σ : finFibrePow c n ⟶ Y)
    (hσ : σ ≫ y = finFibrePow.toBase c n)
    (hI : E.I.comap (mapOnProdOver c σ hσ) = fibrePowOver.tautIdeal c n)
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver c b) (sum : SchemeHomOver y b)
    (hsum : σ ≫ sum.1 = (G.finiteSumMap c q n).1)
    (t : T ⟶ Spec (CommRingCat.of K)) (xs : Fin n → SchemeHomOver t c)
    (A : RelEffCartierDiv c n t)
    (hA : A.I = prodKerGraph c (fun i => (xs i).1) (fun i => (xs i).2)) :
    hE.lift A ≫ sum.1 =
      (G.sumList t (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q)).1 := by
  let v : T ⟶ finFibrePow c n :=
    WidePullback.lift t (fun i => (xs i).1) (fun i => (xs i).2)
  have hv : v ≫ finFibrePow.toBase c n = t := WidePullback.lift_base _ _ _ _
  have hvs : (v ≫ σ) ≫ y = t := by rw [Category.assoc, hσ, hv]
  have hlift : hE.lift A = v ≫ σ := by
    symm
    apply hE.eq_lift hvs
    have hcomp := congrArg RelEffCartierDiv.I (E.pullbackAlong_comp σ hσ v hv)
    change (E.pullbackAlong (v ≫ σ) hvs).I = A.I
    rw [← hcomp]
    change (E.I.comap (mapOnProdOver c σ hσ)).comap (mapOnProdOver c v hv) = A.I
    rw [hI, fibrePowOver.tautIdeal, prodKerGraph_comap_mapOnProdOver, hA]
    exact prodKerGraph_congr c (funext fun i => WidePullback.lift_π _ _ _ _ _) _ _
  have heval := congrArg Subtype.val (G.finiteSumMap_evaluate c q t xs)
  change v ≫ (G.finiteSumMap c q n).1 =
    (G.sumList t (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q)).1 at heval
  rw [hlift, Category.assoc, hsum, heval]

/-- Supported families on the proper curve have the same tuple-evaluation
formula after restriction to the open curve. -/
theorem supportedDivisorSum_evaluate_tuple
    {K : Type u} [Field K] {C B Y T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (U : C.Opens)
    [IsSeparated (U.ι ≫ c)] {n : ℕ}
    {y : Y ⟶ Spec (CommRingCat.of K)} {E : RelEffCartierDiv (U.ι ≫ c) n y}
    (hE : E.IsUniversal) (σ : finFibrePow (U.ι ≫ c) n ⟶ Y)
    (hσ : σ ≫ y = finFibrePow.toBase (U.ι ≫ c) n)
    (hI : E.I.comap (mapOnProdOver (U.ι ≫ c) σ hσ) = fibrePowOver.tautIdeal (U.ι ≫ c) n)
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver (U.ι ≫ c) b) (sum : SchemeHomOver y b)
    (hsum : σ ≫ sum.1 = (G.finiteSumMap (U.ι ≫ c) q n).1)
    (t : T ⟶ Spec (CommRingCat.of K)) (xs : Fin n → SchemeHomOver t (U.ι ≫ c))
    (A : RelEffCartierDiv c n t) (hA : A.SupportedIn U)
    (hAI : (A.restrictToOpen c U hA).I =
      prodKerGraph (U.ι ≫ c) (fun i => (xs i).1) (fun i => (xs i).2)) :
    supportedDivisorSum c U hE sum A hA =
      G.sumList t (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  apply Subtype.ext
  exact divisorSum_evaluate_tuple (U.ι ≫ c) hE σ hσ hI G q sum hsum t xs
    (A.restrictToOpen c U hA) hAI

/-- Over an algebraically closed field every actual supported divisor has a
tuple presentation on which its regular sum is the sum of point values. -/
theorem supportedDivisorSum_exists_geometric_tuple
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (U : C.Opens)
    [IsSeparated (U.ι ≫ c)] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] {n : ℕ}
    {y : Y ⟶ Spec (CommRingCat.of K)} {E : RelEffCartierDiv (U.ι ≫ c) n y}
    (hE : E.IsUniversal) (σ : finFibrePow (U.ι ≫ c) n ⟶ Y)
    (hσ : σ ≫ y = finFibrePow.toBase (U.ι ≫ c) n)
    (hI : E.I.comap (mapOnProdOver (U.ι ≫ c) σ hσ) = fibrePowOver.tautIdeal (U.ι ≫ c) n)
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver (U.ι ≫ c) b) (sum : SchemeHomOver y b)
    (hsum : σ ≫ sum.1 = (G.finiteSumMap (U.ι ≫ c) q n).1)
    {L : Type u} [Field L] [IsAlgClosed L]
    (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (A : RelEffCartierDiv c n t) (hA : A.SupportedIn U) :
    ∃ xs : Fin n → SchemeHomOver t (U.ι ≫ c),
      (A.restrictToOpen c U hA).I =
        prodKerGraph (U.ι ≫ c) (fun i => (xs i).1) (fun i => (xs i).2) ∧
      supportedDivisorSum c U hE sum A hA =
        G.sumList t (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  obtain ⟨a, ha, hA'⟩ :=
    RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed (A.restrictToOpen c U hA)
  let xs : Fin n → SchemeHomOver t (U.ι ≫ c) := fun i => ⟨a i, ha i⟩
  exact ⟨xs, hA', supportedDivisorSum_evaluate_tuple c U hE σ hσ hI G q sum hsum
    t xs A hA hA'⟩

end JacobianVarieties.Albanese
