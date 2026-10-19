/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTracePrincipalDivisor

/-! # Principal evaluation from two finite trace fibres

For the trace coordinate `z`, the difference of the full fibres over `a` and
`b` is the divisor of `(z-a)/(z-b)`. In particular the test function
`g = (z+1)/z` uses the fibres over `-1` and `0`; it does not require a trace
value at infinity.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian JacobianVarieties.Albanese
open AlgebraicCurves.RelativeDivisors.Proofs
open scoped BigOperators CategoryTheory.MonObj
open RelEffCartierDiv_exists_isUniversal_of_isAffine.AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicCurve.RationalFunctionField

/-- Subtracting two linear-polynomial divisors cancels their common pole at
infinity, with no condition that the two finite parameters be distinct. -/
private theorem ord_linearFraction {K : Type*} [Field K]
    (a b : K) (v : Place K (RatFunc K)) :
    v.ord ((RatFunc.X - RatFunc.C a) / (RatFunc.X - RatFunc.C b)) =
      (Finsupp.single (placeOfPoint K a) (1 : ℤ) -
        Finsupp.single (placeOfPoint K b) (1 : ℤ)) v := by
  classical
  have hn (c : K) : RatFunc.X - RatFunc.C c ≠ 0 := by
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero c)
  rw [div_eq_mul_inv, v.ord_mul (hn a) (inv_ne_zero (hn b)), v.ord_inv]
  have ha := ord_X_sub_C K a v
  have hb := ord_X_sub_C K b v
  simp only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
    Finsupp.add_apply] at ha hb
  rw [ha, hb, Finsupp.sub_apply]
  omega

end AlgebraicCurve.RationalFunctionField

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (P : CurveModel K (RatFunc K)) (M : CurveModel K F)
  (φ : RatFunc K →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (hfinite : FiniteAlong K φ)
  (π : M.C ⟶ P.C) (hπ : π ≫ P.toBase = M.toBase)
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : P.C, π.finrank y = n)
  (hgeneric : M.C.fromSpecStalk (genericPoint M.C) ≫ π =
    Spec.map (CommRingCat.ofHom
      (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp P.ffEquiv.symm.toRingHom))) ≫
        P.C.fromSpecStalk (genericPoint P.C))

open Classical in
include hφ hfinite hgeneric in
/-- Two finite fibres give the full divisor of the corresponding linear
fraction, retaining all ramification and nonreduced Cartier multiplicities. -/
theorem rationalFunctionTrace_finite_fibre_divisor (a b : K) :
    let pa := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K a)
    let pb := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K b)
    let A := finiteMapFiberDivisor M.toBase P.toBase π hπ n hn
    let Ea := A.pullbackAlong pa.1 pa.2
    let Eb := A.pullbackAlong pb.1 pb.2
    ∀ w : Place K F,
      ((M.cartierModulus (modulusCurveIdeal Ea) (modulusCurveIdeal_isInvertible Ea)).toDivisor -
        (M.cartierModulus (modulusCurveIdeal Eb)
          (modulusCurveIdeal_isInvertible Eb)).toDivisor) w =
        w.ord (φ ((RatFunc.X - RatFunc.C a) / (RatFunc.X - RatFunc.C b))) := by
  intro pa pb A Ea Eb w
  classical
  have : HasPrincipalDivisors K F :=
    (isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap).toHasPrincipalDivisors
  have ha := CurveModel.finiteMapFiberDivisor_toDivisor P M φ hφ hfinite
    π hπ n hn hgeneric pa
  have hb := CurveModel.finiteMapFiberDivisor_toDivisor P M φ hφ hfinite
    π hπ n hn hgeneric pb
  change ((M.cartierModulus (modulusCurveIdeal Ea)
    (modulusCurveIdeal_isInvertible Ea)).toDivisor -
      (M.cartierModulus (modulusCurveIdeal Eb)
        (modulusCurveIdeal_isInvertible Eb)).toDivisor) w = _
  rw [ha, hb, ← map_sub, Divisor.pullbackAlong_apply φ hφ,
    Place.ord_restrictAlong φ hφ]
  exact congrArg (fun z : ℤ => (Place.ramificationIndexAlong φ w : ℤ) * z) (by
    simpa only [pa, pb, P.pointEquivPlace.apply_symm_apply] using
      (RationalFunctionField.ord_linearFraction a b (w.restrictAlong φ hφ)).symm)

variable [GeometricallyIntegral M.toBase]

open Classical in
include hφ hfinite hgeneric in
/-- Two finite trace values evaluate the principal divisor of their linear
fraction. Only those two points must lie in the actual trace domain. -/
theorem rationalFunctionTrace_finite_principalEvaluation
    (U : M.C.Opens)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) (a b : K) :
    let V := finiteMapTraceLocus M.toBase P.toBase π hπ n hn U
    let τ := finiteCurveTrace M.toBase P.toBase π hπ n hn U ε G q
    ∀ (xa xb : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase)),
      xa.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K a)).1 →
      xb.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K b)).1 →
      commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp xa τ) -
          commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp xb τ) =
        ∑ᶠ w : Place K F,
          w.ord (φ ((RatFunc.X - RatFunc.C a) / (RatFunc.X - RatFunc.C b))) •
            M.regularMapValues U G q w := by
  intro V τ xa xb hxa hxb
  let B := finiteMapFiberDivisor M.toBase P.toBase π hπ n hn
  let A := finiteMapTraceFamily M.toBase P.toBase π hπ n hn U
  let pa := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K a)
  let pb := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K b)
  have hea : A.pullbackAlong xa.1 xa.2 = B.pullbackAlong pa.1 pa.2 :=
    (B.pullbackAlong_comp V.ι rfl xa.1 xa.2).trans
      (ChartAffine.pullbackAlong_congr_hom B hxa
        (by rw [Category.assoc]; exact xa.2) pa.2)
  have heb : A.pullbackAlong xb.1 xb.2 = B.pullbackAlong pb.1 pb.2 :=
    (B.pullbackAlong_comp V.ι rfl xb.1 xb.2).trans
      (ChartAffine.pullbackAlong_congr_hom B hxb
        (by rw [Category.assoc]; exact xb.2) pb.2)
  have hva := finiteCurveTrace_value M P.toBase π hπ n hn U ε G q xa
  have hvb := finiteCurveTrace_value M P.toBase π hπ n hn U ε G q xb
  rw [hea] at hva
  rw [heb] at hvb
  rw [hva, hvb, ← map_sub, Divisor.evaluation_eq_finsum]
  apply congrArg finsum
  funext w
  rw [rationalFunctionTrace_finite_fibre_divisor P M φ hφ hfinite π hπ n hn hgeneric a b w]

open Classical in
include hφ hfinite hgeneric in
/-- For `z = (g-1)⁻¹`, the principal evaluation of `g` is the difference of
the actual trace values at `z = -1` and `z = 0`, both finite parameters. -/
theorem rationalFunctionTrace_reciprocal_principalEvaluation
    (U : M.C.Opens)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom)
    (g : Fˣ) (hg : (g : F) ≠ 1) (hcoordinate : φ RatFunc.X = ((g : F) - 1)⁻¹) :
    let V := finiteMapTraceLocus M.toBase P.toBase π hπ n hn U
    let τ := finiteCurveTrace M.toBase P.toBase π hπ n hn U ε G q
    ∀ (xm x₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase)),
      xm.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K (-1))).1 →
      x₀.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K 0)).1 →
      commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp xm τ) -
          commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x₀ τ) =
        ∑ᶠ w : Place K F, w.ord (g : F) • M.regularMapValues U G q w := by
  intro V τ xm x₀ hxm hx₀
  have h := rationalFunctionTrace_finite_principalEvaluation P M φ hφ hfinite
    π hπ n hn hgeneric U ε G q (-1) 0 xm x₀ hxm hx₀
  have heval : φ ((RatFunc.X - RatFunc.C (-1)) / (RatFunc.X - RatFunc.C 0)) =
      (g : F) := by
    simp only [map_div₀, map_neg, map_one, map_zero, sub_zero,
      sub_neg_eq_add, map_add, hcoordinate]
    field_simp [sub_ne_zero.mpr hg]
    ring
  rw [heval] at h
  exact h

end AlgebraicGeometry.GeneralizedJacobian
