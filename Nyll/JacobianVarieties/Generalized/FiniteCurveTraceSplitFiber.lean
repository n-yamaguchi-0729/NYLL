/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTrace
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.TupleOfSplitDivisor

/-! # Evaluating the actual finite curve trace on a split fibre

The labelled coproduct components construct the full Cartier tuple and
therefore compute the original regular trace, also over nonreduced bases.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

/-- A splitting of the actual restricted fibre divisor computes the regular
trace as the sum of its labelled components, over any test scheme. -/
theorem finiteCurveTrace_evaluate_coprod_iso
    {K : Type u} [Field K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (b : B ⟶ Spec (CommRingCat.of K)) [IsSeparated b]
    (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : C.Opens)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ c))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) :
    let V := finiteMapTraceLocus c b π hπ n hn U
    let A := finiteMapTraceFamily c b π hπ n hn U
    let hA := finiteMapTraceFamily_supported c b π hπ n hn U
    ∀ {T : Scheme.{u}} (a : T ⟶ V),
      let D := (A.pullbackAlong a rfl).restrictToOpen c U (hA.pullbackAlong a rfl)
      ∀ (e : (∐ fun _ : Fin n => T) ≅ D.I.subscheme),
      e.hom ≫ D.I.subschemeι ≫ pullback.snd (U.ι ≫ c) (a ≫ (V.ι ≫ b)) =
        Sigma.desc (fun _ : Fin n => 𝟙 T) →
      ∃ xs : Fin n → SchemeHomOver (a ≫ (V.ι ≫ b)) (U.ι ≫ c),
        (∀ i, (xs i).val = Sigma.ι (fun _ : Fin n => T) i ≫
          e.hom ≫ D.I.subschemeι ≫ pullback.fst (U.ι ≫ c) (a ≫ (V.ι ≫ b))) ∧
        GoodReductionJacobian.schemeHomOverComp a rfl
            (finiteCurveTrace c b π hπ n hn U ε G q) =
          (commGroupRelativeLaw G).sumList (a ≫ (V.ι ≫ b))
            (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  intro V A hA T a D e he
  obtain ⟨xs, hxs, hI⟩ := D.exists_tuple_of_coprod_iso e he
  exact ⟨xs, hxs, finiteCurveTrace_evaluate_tuple c b π hπ n hn U ε G q a xs hI⟩

end AlgebraicGeometry.GeneralizedJacobian
