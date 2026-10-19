/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairSquareMap
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCoordinate
import Nyll.AlgebraicCurves.Models.FunctionFields.FiniteFlatHomAlgHom

/-! # The actual finite projective square map for the same pair function

The smooth-proper extension theorem constructs a morphism between the literal
projective-line models. Its original generic triangle realizes the finite field
homomorphism sending the already selected f to X squared. The next comparison
with the normalized open Kummer cover can therefore use this exact root field.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] Classical.propDecidable

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.KummerTheory

/-- An actual finite flat projective morphism realizes the same pair's square
extension; the root coordinate is X on its literal rational source model. -/
theorem rationalConfiguration_pairFunction_exists_squareModelMap
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
    ∃ eF : RatFunc k ≃ₐ[k] RatFunc k, eF RatFunc.X = f ∧
      ∃ p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C,
        p ≫ (projectiveLineRatFuncModel k).toBase = (projectiveLineRatFuncModel k).toBase ∧
        IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧
        (projectiveLineRatFuncModel k).C.fromSpecStalk
            (genericPoint (projectiveLineRatFuncModel k).C) ≫ p =
          Spec.map (CommRingCat.ofHom
            ((projectiveLineRatFuncModel k).ffEquiv.toRingHom.comp
              ((ratFuncPairSquareHom eF).toRingHom.comp
                (projectiveLineRatFuncModel k).ffEquiv.symm.toRingHom))) ≫
            (projectiveLineRatFuncModel k).C.fromSpecStalk
              (genericPoint (projectiveLineRatFuncModel k).C) ∧
        ratFuncPairSquareHom eF f = (RatFunc.X : RatFunc k) ^ 2 := by
  obtain ⟨eF, hF⟩ := rationalConfiguration_pairFunction_exists_coordinate
    k κ s a b hab V₀ Vinf f harith hgeom
  obtain ⟨p, hp, hfinite, hflat, hfp, _hrank, hgeneric, _hplaces, _hunique⟩ :=
    CurveModel.exists_finite_flat_hom_of_algHom
      (projectiveLineRatFuncModel k) (projectiveLineRatFuncModel k)
      (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF)
      (ratFuncPairSquareHom_finite eF)
  exact ⟨eF, hF, p, hp, hfinite, hflat, hfp, hgeneric,
    ratFuncPairSquareHom_apply_pair eF f hF⟩

end AlgebraicGeometry.ProjSpace
