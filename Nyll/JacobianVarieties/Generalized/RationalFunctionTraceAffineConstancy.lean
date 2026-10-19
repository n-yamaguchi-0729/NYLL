/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceAffineLine
import Nyll.AlgebraicCurves.Geometry.Projective.AffineLineIntegralCancellation

/-! # Constancy on the actual affine chart determines the whole trace

The polynomial chart is dense in the original trace domain. For a separated
target, constancy on that chart therefore proves constancy on the entire
trace domain, with the same value at the polynomial coordinate zero.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Constancy on the actual polynomial chart descends to the original
open trace domain. The constant point is constructed by evaluating at zero. -/
theorem exists_eq_const_of_polynomialChart
    {K : Type u} [Field K]
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom] :
    let P := ProjSpace.projectiveLineRatFuncModel K
    ∀ (V : P.C.Opens) (l : Spec (.of (Polynomial K)) ⟶ V),
      l ≫ V.ι = ProjSpace.projectiveLinePolynomialChart K →
      ∀ τ : SchemeHomOver (V.ι ≫ P.toBase) G.X.hom,
        l ≫ τ.1 = Spec.map (CommRingCat.ofHom (Polynomial.C (R := K))) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫ l ≫ τ.1 →
        ∃ a : SchemeHomOver (𝟙 (Spec (.of K))) G.X.hom,
          τ.1 = (V.ι ≫ P.toBase) ≫ a.1 := by
  intro P V l hl τ hconst
  let a := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫ l ≫ τ.1
  have hlbase : l ≫ (V.ι ≫ P.toBase) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
    rw [← Category.assoc, hl]
    exact ProjSpace.projectiveLinePolynomialChart_comp_π K
  have ha : a ≫ G.X.hom = 𝟙 (Spec (.of K)) := by
    change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫ l ≫ τ.1) ≫
      G.X.hom = _
    rw [Category.assoc, Category.assoc, τ.2, hlbase, ← Spec.map_comp]
    have hc : CommRingCat.ofHom (algebraMap K (Polynomial K)) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : K)) = 𝟙 (CommRingCat.of K) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro c
      exact Polynomial.eval_C
    rw [hc, Spec.map_id]
  have : IsOpenImmersion (l ≫ V.ι) := by
    rw [hl]
    exact ProjSpace.projectiveLinePolynomialChart_isOpenImmersion (k := K)
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l V.ι
  have : Nonempty V := ⟨l (genericPoint (Spec (.of (Polynomial K))))⟩
  have : IsDominant l :=
    ⟨l.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace l⟩
  have hbase : τ.1 ≫ G.X.hom = ((V.ι ≫ P.toBase) ≫ a) ≫ G.X.hom := by
    rw [τ.2, Category.assoc, ha, Category.comp_id]
  refine ⟨⟨a, ha⟩, ?_⟩
  apply ext_of_isDominant_of_isSeparated G.X.hom hbase l
  calc
    l ≫ τ.1 = Spec.map (CommRingCat.ofHom (Polynomial.C (R := K))) ≫ a := hconst
    _ = (l ≫ (V.ι ≫ P.toBase)) ≫ a := by rw [hlbase]
    _ = l ≫ ((V.ι ≫ P.toBase) ≫ a) := Category.assoc _ _ _


end AlgebraicGeometry.GeneralizedJacobian
