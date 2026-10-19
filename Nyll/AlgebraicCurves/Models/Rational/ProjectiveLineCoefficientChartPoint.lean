/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncBaseChange
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints

/-! # The actual coefficient equation for the literal rational generic points

The existing function-field comparison gives the exact equation of scheme
points. This can be used in the projective pullback's universal property before
establishing dominance of a newly constructed base-changed square map.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

/-- The literal generic points commute with the actual projective coefficient
map and the original rational-function coefficient embedding. -/
theorem projectiveLineRatFuncModel_chartPoint_coefficientMap
    (k E : Type) [Field k] [Field E] [Algebra k E] :
    (projectiveLineRatFuncModel E).C.functionFieldChartPoint
        (projectiveLineRatFuncModel E).ffEquiv ≫ map k E 1 =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) (RatFunc E))) ≫
        (projectiveLineRatFuncModel k).C.functionFieldChartPoint
          (projectiveLineRatFuncModel k).ffEquiv :=
  Scheme.functionFieldChartPoint_comp_of_functionFieldMap
    (C := (projectiveLineRatFuncModel k).C)
    (D := (projectiveLineRatFuncModel E).C)
    (projectiveLineRatFuncModel k).ffEquiv (projectiveLineRatFuncModel E).ffEquiv
    (map k E 1) (projectiveLineMap_denseRange k E)
    (algebraMap (RatFunc k) (RatFunc E))
    (projectiveLineRatFuncEquiv_coefficientMap k E)

end AlgebraicGeometry.ProjSpace
