/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCoordinate
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveModelIsoFunctionField

/-! # The actual projective coordinate of the same pair function

The function selected before the Kummer exponent gives an actual base-preserving
projective-line isomorphism. Its pullback of the standard coordinate is proved
to be that same function, using the retained generic-map equation.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] Classical.propDecidable

namespace AlgebraicGeometry.ProjSpace

/-- The already selected pair function is the pullback of X under an actual
projective-line isomorphism over the original arithmetic field. -/
theorem rationalConfiguration_pairFunction_exists_schemeCoordinate
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (s : Finset (Projectivization k (k × k))) (a b : s) (hab : a ≠ b)
    (V₀ Vinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
      (rationalConfigurationOpen s).ι)
    (f : RatFunc k)
    (harith : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀.val then 1 else 0) - (if V = Vinf.val then 1 else 0))
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    ∃ e : (projectiveLineRatFuncModel k).C ≅ (projectiveLineRatFuncModel k).C,
      e.hom ≫ (projectiveLineRatFuncModel k).toBase = (projectiveLineRatFuncModel k).toBase ∧
      ∀ hdense : DenseRange e.hom,
        e.hom.functionFieldMap hdense ((projectiveLineRatFuncModel k).ffEquiv RatFunc.X) =
          (projectiveLineRatFuncModel k).ffEquiv f := by
  obtain ⟨eF, hF⟩ := rationalConfiguration_pairFunction_exists_coordinate
    k κ s a b hab V₀ Vinf f harith hgeom
  obtain ⟨e, he, hfield⟩ := CurveModel.exists_iso_comp_toBase_eq_functionFieldMap_eq
    eF.symm (projectiveLineRatFuncModel k) (projectiveLineRatFuncModel k)
  refine ⟨e, he, fun hdense => ?_⟩
  simpa only [AlgEquiv.symm_symm, hF] using hfield hdense RatFunc.X

end AlgebraicGeometry.ProjSpace
