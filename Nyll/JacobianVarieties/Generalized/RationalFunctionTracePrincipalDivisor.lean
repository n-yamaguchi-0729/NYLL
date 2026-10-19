/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTrace
import Nyll.JacobianVarieties.Generalized.ModulusDivisorSumFieldActual
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.JacobianVarieties.Generalized.DivisorClassPoints
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Models.Ramification.Ramification
import Nyll.AlgebraicCurves.Models.Divisors.CartierPointSums
import Nyll.AlgebraicCurves.Places.Rational.RatFuncOrdXSubC
import Nyll.AlgebraicCurves.RelativeDivisors.Representability.IsUniversalIsAffine

/-! # Full principal-divisor evaluation through the rational-function trace

The graph family has exactly the inverse-image ideal of each target point.
Its regular trace therefore evaluates the full Cartier fibre, including all
ramification multiplicities.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian JacobianVarieties.Albanese
open AlgebraicCurves.RelativeDivisors.Proofs
open scoped BigOperators CategoryTheory.MonObj
open RelEffCartierDiv_exists_isUniversal_of_isAffine.AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem ker_comap_of_isPullback
    {W X Y Z : Scheme.{u}} {i : W ⟶ X} {j : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [IsClosedImmersion g] (h : IsPullback i j f g) : g.ker.comap f = i.ker := by
  calc
    g.ker.comap f = (pullback.fst f g).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion g f).symm
    _ = (h.isoPullback.hom ≫ pullback.fst f g).ker :=
      (Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom _).symm
    _ = i.ker := congrArg Scheme.Hom.ker h.isoPullback_hom_fst

/-- A rational fibre of the actual graph family has the full inverse-image
ideal of the target point. This equality does not discard nilpotents. -/
theorem finiteMapFiberDivisor_curveIdeal
    {K : Type u} [Field K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (b : B ⟶ Spec (CommRingCat.of K))
    [IsSeparated b] (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n)
    (p : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b) :
    modulusCurveIdeal ((finiteMapFiberDivisor c b π hπ n hn).pullbackAlong p.1 p.2) =
      p.1.ker.comap π := by
  let γ := finiteMapGraph c b π hπ
  have : IsClosedImmersion γ := finiteMapGraph_isClosedImmersion c b π hπ
  have : IsClosedImmersion p.1 := by
    have : IsClosedImmersion (p.1 ≫ b) := by
      rw [p.2]
      infer_instance
    exact IsClosedImmersion.of_comp p.1 b
  let m : C ⟶ pullback c b :=
    inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) ≫ mapOnProdOver c p.1 p.2
  have hm₁ : m ≫ pullback.fst c b = 𝟙 C := by
    dsimp only [m]
    rw [Category.assoc, mapOnProdOver_fst, IsIso.inv_hom_id]
  have hid : inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) ≫
      pullback.snd c (𝟙 (Spec (CommRingCat.of K))) = c := by
    rw [IsIso.inv_comp_eq]
    simpa only [Category.comp_id] using
      (pullback.condition (f := c) (g := 𝟙 (Spec (CommRingCat.of K)))).symm
  have hm₂ : m ≫ pullback.snd c b = c ≫ p.1 := by
    dsimp only [m]
    rw [Category.assoc, mapOnProdOver_snd, ← Category.assoc, hid]
  have hf : pullback.fst π p.1 ≫ c = pullback.snd π p.1 := by
    rw [← hπ, ← Category.assoc, pullback.condition, Category.assoc, p.2,
      Category.comp_id]
  have hw : pullback.fst π p.1 ≫ m = pullback.fst π p.1 ≫ γ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hm₁, γ, finiteMapGraph_fst, Category.comp_id]
    · simp only [Category.assoc, hm₂, γ, finiteMapGraph_snd]
      rw [← Category.assoc, hf, pullback.condition]
  have hlegs (s : PullbackCone m γ) : s.fst = s.snd := by
    have h := congrArg (fun r => r ≫ pullback.fst c b) s.condition
    simpa only [Category.assoc, hm₁, γ, finiteMapGraph_fst, Category.comp_id] using h
  have hcone (s : PullbackCone m γ) : s.fst ≫ π = (s.fst ≫ c) ≫ p.1 := by
    have h := congrArg (fun r => r ≫ pullback.snd c b) s.condition
    simp only [Category.assoc, hm₂, γ, finiteMapGraph_snd] at h
    rw [← hlegs s] at h
    exact h.symm.trans (Category.assoc _ _ _).symm
  have hs : IsPullback (pullback.fst π p.1) (pullback.fst π p.1) m γ := by
    apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
    refine PullbackCone.IsLimit.mk hw
      (fun s => pullback.lift s.fst (s.fst ≫ c) (hcone s))
      (fun s => pullback.lift_fst _ _ _) (fun s => ?_) ?_
    · exact (pullback.lift_fst _ _ _).trans (hlegs s)
    · intro s l hl _
      apply (cancel_mono (pullback.fst π p.1)).mp
      exact hl.trans (pullback.lift_fst _ _ _).symm
  rw [modulusCurveIdeal_eq_comap]
  change (γ.ker.comap (mapOnProdOver c p.1 p.2)).comap
    (inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K))))) = _
  rw [← Scheme.IdealSheafData.comap_comp]
  exact (ker_comap_of_isPullback hs).trans
    (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion p.1 π)

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]

/-- The constructed regular trace at a rational parameter evaluates the
entire Cartier fibre in the original target point group. -/
theorem finiteCurveTrace_value
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of K)) [IsSeparated b]
    (π : M.C ⟶ B) (hπ : π ≫ b = M.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : M.C.Opens)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) :
    let V := finiteMapTraceLocus M.toBase b π hπ n hn U
    let A := finiteMapTraceFamily M.toBase b π hπ n hn U
    ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ b),
      commGroupPointValue G (𝟙 _)
          (NeronModelInfra.schemeHomOverComp x
            (finiteCurveTrace M.toBase b π hπ n hn U ε G q)) =
        Divisor.evaluation (M.regularMapValues U G q)
          (M.cartierModulus (modulusCurveIdeal (A.pullbackAlong x.1 x.2))
            (modulusCurveIdeal_isInvertible _)).toDivisor := by
  intro V A x
  let hA := finiteMapTraceFamily_supported M.toBase b π hπ n hn U
  let S := chooseOpenCurveSum M.toBase U (commGroupRelativeLaw G) q n
    (commGroupRelativeLaw_isCommutative G) ε
  change commGroupPointValue G (𝟙 _)
    (GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (supportedDivisorSum M.toBase U S.universal S.sum A hA)) = _
  rw [supportedDivisorSum_naturality]
  exact M.value_supportedDivisorSum U S.universal S.tupleMap S.tupleMap_toBase
    S.tuple_ideal (commGroupRelativeLaw G) q S.sum S.tuple_sum
    (commGroupPointValue G (𝟙 _)) (commGroupPointValue_one G (𝟙 _))
    (commGroupPointValue_mul G (𝟙 _)) (M.regularMapValues U G q)
    (M.regularMapValues_apply U G q) (A.pullbackAlong x.1 x.2)
    (hA.pullbackAlong x.1 x.2)

end AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F₀ F : Type u} [Field F₀] [Field F] [Algebra K F₀] [Algebra K F]

/-- The specified generic map determines the restriction of every actual
rational point. The comparison is obtained from the constructed model map
and its proved uniqueness, rather than assumed for the finite morphism. -/
theorem pointEquivPlace_comp_of_generic
    (P : CurveModel K F₀) (M : CurveModel K F)
    (φ : F₀ →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (hfinite : FiniteAlong K φ)
    (π : M.C ⟶ P.C)
    (hgeneric : M.C.fromSpecStalk (genericPoint M.C) ≫ π =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp P.ffEquiv.symm.toRingHom))) ≫
          P.C.fromSpecStalk (genericPoint P.C))
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase)
    (hyx : y.1 ≫ π = x.1) :
    (M.pointEquivPlace y).restrictAlong φ hφ = P.pointEquivPlace x := by
  obtain ⟨π₀, _, _, _, _, _, hgeneric₀, hclosed, huniq⟩ :=
    P.exists_finite_flat_hom_of_algHom M φ hφ hfinite
  have he : π = π₀ := huniq π (hgeneric.trans hgeneric₀.symm)
  subst π
  let z := pointEquivClosedPoint M.toBase y
  obtain ⟨hz, hplace⟩ := hclosed z
  have hpoint : (⟨π₀ z.1, hz⟩ : closedPoints P.C) =
      pointEquivClosedPoint P.toBase x := by
    apply Subtype.ext
    exact congrArg (fun r : Spec (CommRingCat.of K) ⟶ P.C =>
      r (IsLocalRing.closedPoint K)) hyx
  exact hplace.symm.trans (congrArg P.placeOfPoint hpoint)

private theorem invertibleIdeal_value_congr
    {X : Scheme.{u}} {A : Type*}
    (f : ∀ I : X.IdealSheafData, I.IsInvertible → A)
    {I J : X.IdealSheafData} (h : I = J) (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    f I hI = f J hJ := by
  subst J
  rfl

private theorem cartierModulus_pow (M : CurveModel K F)
    (I : M.C.IdealSheafData) (hI : I.IsInvertible) (n : ℕ) :
    M.cartierModulus (I ^ n) (hI.pow n) = n • M.cartierModulus I hI := by
  induction n with
  | zero =>
    have h := M.cartierModulus_pointIdealProduct 0
    simpa only [pow_zero, pointIdealProduct, Finsupp.support_zero, Finset.prod_empty,
      zero_nsmul] using h
  | succ n ih =>
    calc
      _ = M.cartierModulus (I ^ n * I) ((hI.pow n).mul hI) :=
        invertibleIdeal_value_congr (fun J hJ => M.cartierModulus J hJ)
          (pow_succ I n) (hI.pow (n + 1)) ((hI.pow n).mul hI)
      _ = M.cartierModulus (I ^ n) (hI.pow n) + M.cartierModulus I hI :=
        M.cartierModulus_mul (I ^ n) I (hI.pow n) hI
      _ = _ := by rw [ih, succ_nsmul]

/-- The actual fibre divisor is the pullback of its target point divisor,
with ramification index as the full coefficient, including inseparable maps. -/
theorem finiteMapFiberDivisor_toDivisor
    (P : CurveModel K F₀) (M : CurveModel K F)
    (φ : F₀ →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (hfinite : FiniteAlong K φ)
    (π : M.C ⟶ P.C) (hπ : π ≫ P.toBase = M.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : P.C, π.finrank y = n)
    (hgeneric : M.C.fromSpecStalk (genericPoint M.C) ≫ π =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp P.ffEquiv.symm.toRingHom))) ≫
          P.C.fromSpecStalk (genericPoint P.C))
    (p : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase) :
    let E := (AlgebraicGeometry.GeneralizedJacobian.finiteMapFiberDivisor
      M.toBase P.toBase π hπ n hn).pullbackAlong p.1 p.2
    let _ : HasPrincipalDivisors K F :=
      (isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase M.ffEquiv M.ffEquiv_algebraMap).toHasPrincipalDivisors
    (M.cartierModulus (AlgebraicGeometry.GeneralizedJacobian.modulusCurveIdeal E)
      (AlgebraicGeometry.GeneralizedJacobian.modulusCurveIdeal_isInvertible E)).toDivisor =
        Divisor.pullbackAlong φ hφ (Finsupp.single (P.pointEquivPlace p) 1) := by
  intro E hprincipal
  classical
  let _ : Algebra F₀ F := algebraAlong φ
  have : IsScalarTower K F₀ F := isScalarTower_along φ
  have : Algebra.IsIntegral F₀ F := isIntegral_along φ hφ
  have : IsCurveOver K F₀ :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      P.toBase P.ffEquiv P.ffEquiv_algebraMap
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F₀ := by
    let _ : Algebra K P.C.functionField := P.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv P.ffAlgEquiv).mpr
      (essFiniteType_functionField P.toBase)
  have : Algebra.EssFiniteType K F := by
    let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  have hplace (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
      (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase)
      (hyx : y.1 ≫ π = x.1) :
      (M.pointEquivPlace y).restrict F₀ = P.pointEquivPlace x :=
    pointEquivPlace_comp_of_generic P M φ hφ hfinite π hgeneric y x hyx
  have hker := P.ker_comap_eq_prod_ker_pow_ramificationIndex M π hπ hplace p
  let W := (P.pointEquivPlace p).fiber F
  let J : Place K F → M.C.IdealSheafData := fun w =>
    (M.pointEquivPlace.symm w).1.ker ^ w.ramificationIndex F₀
  have hJ (w : Place K F) : (J w).IsInvertible :=
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id _ (M.pointEquivPlace.symm w).2).pow _
  have he := (AlgebraicGeometry.GeneralizedJacobian.finiteMapFiberDivisor_curveIdeal
    M.toBase P.toBase π hπ n hn p).trans hker
  have hprod : (∏ w ∈ W, J w).IsInvertible :=
    he ▸ AlgebraicGeometry.GeneralizedJacobian.modulusCurveIdeal_isInvertible E
  have hsum := M.cartierModulus_finset_prod W J hJ
  have hsub :
      (⟨AlgebraicGeometry.GeneralizedJacobian.modulusCurveIdeal E,
        AlgebraicGeometry.GeneralizedJacobian.modulusCurveIdeal_isInvertible E⟩ :
          {I : M.C.IdealSheafData // I.IsInvertible}) =
        ⟨∏ w ∈ W, J w, hprod⟩ := Subtype.ext he
  have hmod := (congrArg M.cartierIdealEquiv hsub).trans hsum
  have hcoord (w : Place K F) :
      M.cartierModulus (J w) (hJ w) =
        Finsupp.single w (w.ramificationIndex F₀) := by
    have hpoint := Scheme.Hom.isInvertible_ker_of_comp_eq_id
      (M.pointEquivPlace.symm w).1 (M.pointEquivPlace.symm w).2
    rw [cartierModulus_pow M (M.pointEquivPlace.symm w).1.ker hpoint,
      M.cartierModulus_point, M.pointEquivPlace.apply_symm_apply,
      Finsupp.smul_single, nsmul_eq_mul, Nat.cast_id, mul_one]
  have hnat : M.cartierModulus
      (AlgebraicGeometry.GeneralizedJacobian.modulusCurveIdeal E)
      (AlgebraicGeometry.GeneralizedJacobian.modulusCurveIdeal_isInvertible E) =
        ∑ w ∈ W, Finsupp.single w (w.ramificationIndex F₀) :=
    hmod.trans (Finset.sum_congr rfl fun w _ => hcoord w)
  rw [hnat, Divisor.pullbackAlong_single]
  ext w
  simp only [Modulus.toDivisor_apply, Finsupp.finsetSum_apply, Nat.cast_sum]
  change (∑ z ∈ W, ((Finsupp.single z (z.ramificationIndex F₀) w : ℕ) : ℤ)) =
    ∑ z ∈ W, (Finsupp.single z (1 * (z.ramificationIndex F₀ : ℤ)) w)
  apply Finset.sum_congr rfl
  intro z _
  by_cases hzw : z = w
  · subst z
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same, one_mul]
  · rw [Finsupp.single_eq_of_ne' hzw, Finsupp.single_eq_of_ne' hzw, Nat.cast_zero]

end AlgebraicCurve.CurveModel

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
/-- Zero fibre minus pole fibre is exactly the divisor of the prescribed
rational function. All Cartier and inseparable multiplicities are retained. -/
theorem rationalFunctionTrace_fibre_divisor :
    let p₀ := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K 0)
    let pInf := P.pointEquivPlace.symm (RationalFunctionField.placeInfty K)
    let A := finiteMapFiberDivisor M.toBase P.toBase π hπ n hn
    let E₀ := A.pullbackAlong p₀.1 p₀.2
    let EInf := A.pullbackAlong pInf.1 pInf.2
    ∀ w : Place K F,
      ((M.cartierModulus (modulusCurveIdeal E₀) (modulusCurveIdeal_isInvertible E₀)).toDivisor -
        (M.cartierModulus (modulusCurveIdeal EInf)
          (modulusCurveIdeal_isInvertible EInf)).toDivisor) w =
          w.ord (φ RatFunc.X) := by
  intro p₀ pInf A E₀ EInf w
  classical
  have : HasPrincipalDivisors K F :=
    (isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap).toHasPrincipalDivisors
  have h₀ := CurveModel.finiteMapFiberDivisor_toDivisor P M φ hφ hfinite
    π hπ n hn hgeneric p₀
  have hInf := CurveModel.finiteMapFiberDivisor_toDivisor P M φ hφ hfinite
    π hπ n hn hgeneric pInf
  change ((M.cartierModulus (modulusCurveIdeal E₀)
    (modulusCurveIdeal_isInvertible E₀)).toDivisor -
      (M.cartierModulus (modulusCurveIdeal EInf)
        (modulusCurveIdeal_isInvertible EInf)).toDivisor) w = _
  rw [h₀, hInf, ← map_sub, Divisor.pullbackAlong_apply φ hφ,
    Place.ord_restrictAlong φ hφ]
  have h := RationalFunctionField.ord_X_sub_C K 0 (w.restrictAlong φ hφ)
  exact congrArg (fun z : ℤ => (Place.ramificationIndexAlong φ w : ℤ) * z) (by
    simpa only [p₀, pInf, P.pointEquivPlace.apply_symm_apply, Polynomial.C_0, sub_zero,
      RatFunc.algebraMap_X, Finsupp.single_neg, ← sub_eq_add_neg] using h.symm)

variable [GeometricallyIntegral M.toBase]

open Classical in
include hφ hfinite hgeneric in
/-- The two actual trace values evaluate the full principal divisor once
the zero and pole points are lifted to the trace domain. -/
theorem rationalFunctionTrace_principalEvaluation
    (U : M.C.Opens)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) :
    let V := finiteMapTraceLocus M.toBase P.toBase π hπ n hn U
    let τ := finiteCurveTrace M.toBase P.toBase π hπ n hn U ε G q
    ∀ (x₀ xInf : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase)),
      x₀.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K 0)).1 →
      xInf.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeInfty K)).1 →
      commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x₀ τ) -
          commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp xInf τ) =
        ∑ᶠ w : Place K F, w.ord (φ RatFunc.X) • M.regularMapValues U G q w := by
  intro V τ x₀ xInf hx₀ hxInf
  let B := finiteMapFiberDivisor M.toBase P.toBase π hπ n hn
  let A := finiteMapTraceFamily M.toBase P.toBase π hπ n hn U
  let p₀ := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K 0)
  let pInf := P.pointEquivPlace.symm (RationalFunctionField.placeInfty K)
  have he₀ : A.pullbackAlong x₀.1 x₀.2 = B.pullbackAlong p₀.1 p₀.2 :=
    (B.pullbackAlong_comp V.ι rfl x₀.1 x₀.2).trans
      (ChartAffine.pullbackAlong_congr_hom B hx₀
        (by rw [Category.assoc]; exact x₀.2) p₀.2)
  have heInf : A.pullbackAlong xInf.1 xInf.2 = B.pullbackAlong pInf.1 pInf.2 :=
    (B.pullbackAlong_comp V.ι rfl xInf.1 xInf.2).trans
      (ChartAffine.pullbackAlong_congr_hom B hxInf
        (by rw [Category.assoc]; exact xInf.2) pInf.2)
  have hv₀ := finiteCurveTrace_value M P.toBase π hπ n hn U ε G q x₀
  have hvInf := finiteCurveTrace_value M P.toBase π hπ n hn U ε G q xInf
  rw [he₀] at hv₀
  rw [heInf] at hvInf
  rw [hv₀, hvInf, ← map_sub, Divisor.evaluation_eq_finsum]
  apply congrArg finsum
  funext w
  rw [rationalFunctionTrace_fibre_divisor P M φ hφ hfinite π hπ n hn hgeneric w]

omit [GeometricallyIntegral M.toBase] in
include hφ hfinite hgeneric in
private theorem rationalFunctionTrace_lift_zero_or_pole
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : ∀ w : Place K F, (M.placeEquiv.symm w).1 ∉ U → w.ord (φ RatFunc.X) = 0)
    (p : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase)
    (hp : (P.pointEquivPlace p).ord RatFunc.X ≠ 0) :
    let V := finiteMapTraceLocus M.toBase P.toBase π hπ n hn U
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase),
      x.1 ≫ V.ι = p.1 := by
  intro V
  classical
  let _ : Algebra (RatFunc K) F := algebraAlong φ
  have : IsScalarTower K (RatFunc K) F := isScalarTower_along φ
  have : Algebra.IsIntegral (RatFunc K) F := isIntegral_along φ hφ
  have hmem : p.1 (IsLocalRing.closedPoint K) ∈ V := by
    apply (mem_finiteMapTraceLocus_iff M.toBase P.toBase π hπ n hn U _).mpr
    intro z hz
    by_contra hzU
    have hη : genericPoint M.C ∈ U :=
      ((genericPoint_spec M.C).mem_open_set_iff U.isOpen).mpr
        ⟨hU.choose, trivial, hU.choose_spec⟩
    have hzc : IsClosed ({z} : Set M.C) :=
      isClosed_singleton_of_ne_genericPoint M.toBase z (fun h => hzU (h ▸ hη))
    let y := (pointEquivClosedPoint M.toBase).symm ⟨z, hzc⟩
    have hy : pointEquivClosedPoint M.toBase y = ⟨z, hzc⟩ :=
      (pointEquivClosedPoint M.toBase).apply_symm_apply _
    let yp : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase :=
      ⟨y.1 ≫ π, by rw [Category.assoc, hπ]; exact y.2⟩
    have hyp : yp = p := by
      apply (pointEquivClosedPoint P.toBase).injective
      apply Subtype.ext
      change π (y.1 (IsLocalRing.closedPoint K)) = p.1 (IsLocalRing.closedPoint K)
      rw [show y.1 (IsLocalRing.closedPoint K) = z from congrArg Subtype.val hy]
      exact hz
    have hr := CurveModel.pointEquivPlace_comp_of_generic P M φ hφ hfinite
      π hgeneric y p (congrArg Subtype.val hyp)
    have hpoint : (M.placeEquiv.symm (M.pointEquivPlace y)).1 = z := by
      change (M.placeEquiv.symm (M.placeEquiv (pointEquivClosedPoint M.toBase y))).1 = z
      rw [M.placeEquiv.symm_apply_apply, hy]
    have hzord := hboundary (M.pointEquivPlace y) (by rw [hpoint]; exact hzU)
    have hord := Place.ord_restrictAlong φ hφ (M.pointEquivPlace y) RatFunc.X
    rw [hr] at hord
    have he : (Place.ramificationIndexAlong φ (M.pointEquivPlace y) : ℤ) ≠ 0 := by
      have hepos : 0 < Place.ramificationIndexAlong φ (M.pointEquivPlace y) :=
        (M.pointEquivPlace y).ramificationIndex_pos (F := RatFunc K)
      exact_mod_cast hepos.ne'
    exact (mul_ne_zero he hp) (hord.symm.trans hzord)
  have hrange : Set.range p.1 ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hz]
    exact hmem
  let x := IsOpenImmersion.lift V.ι p.1 hrange
  have hx : x ≫ V.ι = p.1 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨x, ?_⟩, hx⟩
  rw [← Category.assoc, hx, p.2]

end AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F)

open Classical in
/-- An admissible nonconstant test function constructs an actual trace with
both zero and pole parameters in its domain, and their difference is the
full principal-divisor evaluation of the original group-valued map. -/
theorem exists_rationalFunctionTrace_principalEvaluation
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)
    (g : Fˣ) (hgnonconstant : (g : F) ∉ Set.range (algebraMap K F))
    (hg : (M.functionFieldModulus D).CongruentOne (g : F)) :
    let _ : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
    ∃ (P : CurveModel K (RatFunc K)) (φ : RatFunc K →ₐ[K] F)
      (π : M.C ⟶ P.C) (hπ : π ≫ P.toBase = M.toBase)
      (_ : IsFinite π) (_ : Flat π) (_ : LocallyOfFinitePresentation π)
      (hn : ∀ y : P.C, π.finrank y = finrankAlong K φ),
      φ RatFunc.X = (g : F) ∧
      let U := modulusComplement (modulusCurveMap D)
      let V := finiteMapTraceLocus M.toBase P.toBase π hπ (finrankAlong K φ) hn U
      ∃ (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase))
        (x₀ xInf : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase)),
        x₀.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K 0)).1 ∧
        xInf.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeInfty K)).1 ∧
        let τ := finiteCurveTrace M.toBase P.toBase π hπ (finrankAlong K φ) hn U ε G q
        commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x₀ τ) -
            commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp xInf τ) =
          ∑ᶠ w : Place K F, w.ord (g : F) • M.regularMapValues U G q w := by
  intro hgeom
  classical
  obtain ⟨P, φ, hφX, hφ, hfinite, π, hπ, hfin, hflat, hlfp, hn, hgeneric⟩ :=
    exists_finiteFlatMap_of_nonconstant M (g : F) hgnonconstant
  let U := modulusComplement (modulusCurveMap D)
  have : Nonempty U := modulusComplement_nonempty M.toBase D
  have hU : (U : Set M.C).Nonempty :=
    ⟨(Classical.choice (inferInstance : Nonempty U)).1,
      (Classical.choice (inferInstance : Nonempty U)).2⟩
  have hboundary (w : Place K F) (hw : (M.placeEquiv.symm w).1 ∉ U) :
      w.ord (φ RatFunc.X) = 0 := by
    rw [hφX]
    apply hg.ord_eq_zero w
    intro hz
    exact hw ((M.cartierModulus_eq_zero_iff (modulusCurveIdeal D)
      (modulusCurveIdeal_isInvertible D) w).mp hz)
  let p₀ := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K 0)
  let pInf := P.pointEquivPlace.symm (RationalFunctionField.placeInfty K)
  have h₀ : (P.pointEquivPlace p₀).ord RatFunc.X ≠ 0 := by
    have h := RationalFunctionField.ord_X_sub_C K 0 (RationalFunctionField.placeOfPoint K 0)
    simp only [Polynomial.C_0, sub_zero, RatFunc.algebraMap_X, Finsupp.add_apply,
      Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (RationalFunctionField.placeOfPoint_ne_placeInfty K 0),
      add_zero] at h
    rw [P.pointEquivPlace.apply_symm_apply]
    exact h.trans_ne one_ne_zero
  have hInf : (P.pointEquivPlace pInf).ord RatFunc.X ≠ 0 := by
    have h := RationalFunctionField.ord_X_sub_C K 0 (RationalFunctionField.placeInfty K)
    simp only [Polynomial.C_0, sub_zero, RatFunc.algebraMap_X, Finsupp.add_apply,
      Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (RationalFunctionField.placeOfPoint_ne_placeInfty K 0).symm,
      zero_add] at h
    rw [P.pointEquivPlace.apply_symm_apply]
    exact h.trans_ne (neg_ne_zero.mpr one_ne_zero)
  obtain ⟨x₀, hx₀⟩ := rationalFunctionTrace_lift_zero_or_pole P M φ hφ hfinite
    π hπ (finrankAlong K φ) hn hgeneric U hU hboundary p₀ h₀
  obtain ⟨xInf, hxInf⟩ := rationalFunctionTrace_lift_zero_or_pole P M φ hφ hfinite
    π hπ (finrankAlong K φ) hn hgeneric U hU hboundary pInf hInf
  obtain ⟨ε₀⟩ := modulusComplement_point M.toBase D
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase) :=
    ⟨ε₀.left, Over.w ε₀⟩
  refine ⟨P, φ, π, hπ, hfin, hflat, hlfp, hn, hφX, ε, x₀, xInf, hx₀, hxInf, ?_⟩
  have h := rationalFunctionTrace_principalEvaluation P M φ hφ hfinite π hπ
    (finrankAlong K φ) hn hgeneric U ε G q x₀ xInf hx₀ hxInf
  rw [hφX] at h
  exact h

end AlgebraicGeometry.GeneralizedJacobian
