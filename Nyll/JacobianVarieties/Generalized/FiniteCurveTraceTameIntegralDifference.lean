/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GenericTracePoint
import Nyll.JacobianVarieties.Generalized.FiniteCurveTracePowerSeriesBlocks
import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceBlockAdditivity
import Nyll.JacobianVarieties.Generalized.RegularCartierBlockIntegralDifference
import Nyll.JacobianVarieties.Generalized.FormalBoundaryBlockEvaluation
import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceDomain
import Nyll.AlgebraicCurves.Places.Degree.CompletedRegularCoefficientMap
import Nyll.AlgebraicCurves.Places.Degree.TameBoundaryCompletedEmbeddings
import Nyll.AlgebraicCurves.Places.Orders.TameReciprocalInfinity
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField

/-! # The integral difference of the original finite curve trace

The whole integral point is the product of the actual Henselian regular
block point and the actual completed boundary block point. The full
Cartier ideal decomposition computes that product as the original trace
difference. Both block constructions use the same completed-base map and
the same Laurent valuation ring. The pole bound is chosen before the
finite map and exact-contact test function.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian JacobianVarieties.Albanese
open scoped WithZero AlgebraicCurve.Place CategoryTheory.MonObj
open scoped AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem regular_base_map_comparison
    {K B : Type u} [Field K] [Field B] [Algebra K B]
    (v : AlgebraicCurve.Place K B)
    (E : v.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : v.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x)
    (i : LaurentSeries K →ₐ[K] LaurentSeries K) :
    let O := v.powerSeriesEquivCompletionIntegers E hE
    let g := Spec.map (CommRingCat.ofHom
      ((algebraMap v.adicCompletionIntegers v.adicCompletion).comp O.toRingHom))
    let τ := (LaurentSeries.regularReciprocalDeformation i).comp E.toAlgHom
    let j := LaurentSeries.regularBlockCoefficients i
    let γ := formalBlockCoefficientMap j
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ g =
      (γ ≫ formalBlockBaseMap (PowerSeries.reciprocalParameterDeformation (K := K))).left := by
  intro O g τ j γ
  change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ g =
    Spec.map (CommRingCat.ofHom (PowerSeries.map j.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom PowerSeries.reciprocalParameterDeformation.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change LaurentSeries.regularReciprocalDeformation i
    (E (algebraMap v.adicCompletionIntegers v.adicCompletion (O f))) = _
  rw [AlgebraicCurve.Place.powerSeriesEquivCompletionIntegers_coe,
    E.apply_symm_apply, LaurentSeries.regularReciprocalDeformation_coe]
  rfl

private theorem constant_base_map_comparison
    {K B : Type u} [Field K] [Field B] [Algebra K B]
    (v : AlgebraicCurve.Place K B)
    (E : v.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : v.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x)
    (i : LaurentSeries K →ₐ[K] LaurentSeries K) :
    let O := v.powerSeriesEquivCompletionIntegers E hE
    let g := Spec.map (CommRingCat.ofHom
      ((algebraMap v.adicCompletionIntegers v.adicCompletion).comp O.toRingHom))
    let τ₀ := (IsScalarTower.toAlgHom K (LaurentSeries K)
      (PowerSeries (LaurentSeries K))).comp (i.comp E.toAlgHom)
    let γ := formalBlockCoefficientMap (LaurentSeries.regularBlockCoefficients i)
    Spec.map (CommRingCat.ofHom τ₀.toRingHom) ≫ g =
      (γ ≫ formalBlockBaseMap (formalBlockConstantInclusion (K := K))).left := by
  intro O g τ₀ γ
  change Spec.map (CommRingCat.ofHom τ₀.toRingHom) ≫ g =
    Spec.map (CommRingCat.ofHom (PowerSeries.map
      (LaurentSeries.regularBlockCoefficients i).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom PowerSeries.C)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change PowerSeries.C (i (E
    (algebraMap v.adicCompletionIntegers v.adicCompletion (O f)))) = _
  rw [AlgebraicCurve.Place.powerSeriesEquivCompletionIntegers_coe, E.apply_symm_apply]
  change PowerSeries.C (i (HahnSeries.ofPowerSeries ℤ K f)) =
    PowerSeries.map (LaurentSeries.regularBlockCoefficients i).toRingHom (PowerSeries.C f)
  rw [PowerSeries.map_C]
  rfl

private theorem pullbackAlong_congr_map
    {S C R T : Scheme.{u}} {c : C ⟶ S} {r : R ⟶ S} {t : T ⟶ S} {n : ℕ}
    (D : RelEffCartierDiv c n r) {a b : T ⟶ R} (h : a = b)
    (ha : a ≫ r = t) (hb : b ≫ r = t) :
    D.pullbackAlong a ha = D.pullbackAlong b hb := by
  cases h
  rfl

private theorem supported_point_congr
    {K : Type u} [Field K] {C T : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (U : C.Opens)
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {n : ℕ}
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q n)
    {t : T ⟶ Spec (.of K)} (A B : RelEffCartierDiv c n t)
    (h : A = B) (hA : A.SupportedIn U) :
    commGroupPointEquiv G t (supportedDivisorSum c U s.universal s.sum A hA) =
      commGroupPointEquiv G t (supportedDivisorSum c U s.universal s.sum B (h ▸ hA)) := by
  cases h
  rfl

private theorem supported_difference_blocks_of_degree
    {K : Type u} [Field K] {C R T : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {n m k : ℕ} (hdegree : n = m + k)
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q n)
    (s₀ : OpenCurveSum c U (commGroupRelativeLaw G) q m)
    (s₁ : OpenCurveSum c U (commGroupRelativeLaw G) q k)
    {r : R ⟶ Spec (.of K)} {t : T ⟶ Spec (.of K)}
    (D : RelEffCartierDiv c n r)
    (D₀ : RelEffCartierDiv c m r) (D₁ : RelEffCartierDiv c k r)
    (hI : D.I = D₀.I * D₁.I)
    (a b : T ⟶ R) (ha : a ≫ r = t) (hb : b ≫ r = t)
    (hDa : (D.pullbackAlong a ha).SupportedIn U)
    (hDb : (D.pullbackAlong b hb).SupportedIn U)
    (h₀a : (D₀.pullbackAlong a ha).SupportedIn U)
    (h₁a : (D₁.pullbackAlong a ha).SupportedIn U)
    (h₀b : (D₀.pullbackAlong b hb).SupportedIn U)
    (h₁b : (D₁.pullbackAlong b hb).SupportedIn U) :
      commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong a ha) hDa) *
        (commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong b hb) hDb))⁻¹ =
      (commGroupPointEquiv G t
          (supportedDivisorSum c U s₀.universal s₀.sum (D₀.pullbackAlong a ha) h₀a) *
        (commGroupPointEquiv G t
          (supportedDivisorSum c U s₀.universal s₀.sum (D₀.pullbackAlong b hb) h₀b))⁻¹) *
      (commGroupPointEquiv G t
          (supportedDivisorSum c U s₁.universal s₁.sum (D₁.pullbackAlong a ha) h₁a) *
        (commGroupPointEquiv G t
          (supportedDivisorSum c U s₁.universal s₁.sum (D₁.pullbackAlong b hb) h₁b))⁻¹) := by
  subst n
  obtain ⟨_, _, _, _, h⟩ := supportedDivisorSum_pullback_difference_blocks
    c U G q s s₀ s₁ D D₀ D₁ hI a b ha hb hDa hDb
  exact h

private theorem point_difference_congr
    {S : Scheme.{u}} (G : CommGrp (Over S)) {T : Over S}
    (lhs : T.left ⟶ G.X.left) (a b a' b' : T ⟶ G.X)
    (h : lhs = (a * b⁻¹).left) (ha : a = a') (hb : b = b') :
    lhs = (a' * b'⁻¹).left :=
  h.trans (congrArg (fun f : T ⟶ G.X => f.left)
    (congrArg₂ (fun f g : T ⟶ G.X => f * g⁻¹) ha hb))

private theorem integral_product_of_block_points
    {S : Scheme.{u}} (G : CommGrp (Over S))
    {R T Tred F W : Over S} (inc : T ⟶ R) (red : Tred ⟶ R)
    (a b : T ⟶ F) (genericMap : F ⟶ W) (tracePoint : W ⟶ G.X)
    (pR pB : R ⟶ G.X) (sumA sumB regular boundary : T ⟶ G.X)
    (htraceA : (a ≫ genericMap) ≫ tracePoint = sumA)
    (htraceB : (b ≫ genericMap) ≫ tracePoint = sumB)
    (hsums : sumA * sumB⁻¹ = regular * boundary)
    (hR : inc.left ≫ pR.left = regular.left)
    (hB : inc.left ≫ pB.left = boundary.left)
    (hRred : red.left ≫ pR.left = (1 : Tred ⟶ G.X).left)
    (hBred : red.left ≫ pB.left = (1 : Tred ⟶ G.X).left) :
    inc.left ≫ (pR * pB).left =
      ((a ≫ (genericMap ≫ tracePoint)) * (b ≫ (genericMap ≫ tracePoint))⁻¹).left ∧
    red.left ≫ (pR * pB).left = (1 : Tred ⟶ G.X).left := by
  have hiR : inc ≫ pR = regular := by
    apply Over.OverMorphism.ext
    exact hR
  have hiB : inc ≫ pB = boundary := by
    apply Over.OverMorphism.ext
    exact hB
  have hi : inc ≫ (pR * pB) =
      (a ≫ (genericMap ≫ tracePoint)) * (b ≫ (genericMap ≫ tracePoint))⁻¹ := by
    rw [MonObj.comp_mul, hiR, hiB, ← hsums, ← htraceA, ← htraceB]
    simp only [Category.assoc]
  have hrR : red ≫ pR = 1 := by
    apply Over.OverMorphism.ext
    exact hRred
  have hrB : red ≫ pB = 1 := by
    apply Over.OverMorphism.ext
    exact hBred
  have hr : red ≫ (pR * pB) = 1 := by
    rw [MonObj.comp_mul, hrR, hrB, one_mul]
  exact ⟨congrArg (fun f : T ⟶ G.X => f.left) hi,
    congrArg (fun f : Tred ⟶ G.X => f.left) hr⟩

private theorem integral_trace_difference_of_completed_blocks
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    {R E O T Tred F W : Over (Spec (.of K))} {n m k : ℕ}
    (hdegree : n = m + k)
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q n)
    (s₀ : OpenCurveSum c U (commGroupRelativeLaw G) q m)
    (s₁ : OpenCurveSum c U (commGroupRelativeLaw G) q k)
    (D : RelEffCartierDiv c n R.hom)
    (D₀ : RelEffCartierDiv c m R.hom) (D₁ : RelEffCartierDiv c k R.hom)
    (hmul : D.I = D₀.I * D₁.I) (hD₀U : D₀.SupportedIn U)
    (g : E ⟶ R) (Dg : RelEffCartierDiv c k E.hom)
    (hDg : Dg = D₁.pullbackAlong g.left (Over.w g))
    (fa fb : T ⟶ E) (a b : T ⟶ R)
    (hfa : fa.left ≫ g.left = a.left) (hfb : fb.left ≫ g.left = b.left)
    (hA : (Dg.pullbackAlong fa.left (Over.w fa)).SupportedIn U)
    (hA₀ : (Dg.pullbackAlong fb.left (Over.w fb)).SupportedIn U)
    (inc : T ⟶ O) (red : Tred ⟶ O) (pR pB : O ⟶ G.X)
    (hpR : inc.left ≫ pR.left =
      (commGroupPointEquiv G T.hom
        (supportedDivisorSum c U s₀.universal s₀.sum
          (D₀.pullbackAlong a.left (Over.w a)) (hD₀U.pullbackAlong a.left (Over.w a))) *
        (commGroupPointEquiv G T.hom
          (supportedDivisorSum c U s₀.universal s₀.sum
            (D₀.pullbackAlong b.left (Over.w b))
            (hD₀U.pullbackAlong b.left (Over.w b))))⁻¹).left)
    (hpB : inc.left ≫ pB.left =
      (commGroupPointEquiv G T.hom
        (supportedDivisorSum c U s₁.universal s₁.sum
          (Dg.pullbackAlong fa.left (Over.w fa)) hA) *
        (commGroupPointEquiv G T.hom
          (supportedDivisorSum c U s₁.universal s₁.sum
            (Dg.pullbackAlong fb.left (Over.w fb)) hA₀))⁻¹).left)
    (hpRred : red.left ≫ pR.left = (1 : Tred ⟶ G.X).left)
    (hpBred : red.left ≫ pB.left = (1 : Tred ⟶ G.X).left)
    (traceA traceB : T ⟶ F) (genericMap : F ⟶ W) (tracePoint : W ⟶ G.X)
    (hDa : (D.pullbackAlong a.left (Over.w a)).SupportedIn U)
    (hDb : (D.pullbackAlong b.left (Over.w b)).SupportedIn U)
    (htraceA : (traceA ≫ genericMap) ≫ tracePoint =
      commGroupPointEquiv G T.hom
        (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong a.left (Over.w a)) hDa))
    (htraceB : (traceB ≫ genericMap) ≫ tracePoint =
      commGroupPointEquiv G T.hom
        (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong b.left (Over.w b)) hDb)) :
    inc.left ≫ (pR * pB).left =
      ((traceA ≫ (genericMap ≫ tracePoint)) *
        (traceB ≫ (genericMap ≫ tracePoint))⁻¹).left ∧
      red.left ≫ (pR * pB).left = (1 : Tred ⟶ G.X).left := by
  have hpullA : Dg.pullbackAlong fa.left (Over.w fa) =
      D₁.pullbackAlong a.left (Over.w a) := by
    rw [hDg, RelEffCartierDiv.pullbackAlong_comp]
    exact pullbackAlong_congr_map D₁ hfa _ _
  have hpullB : Dg.pullbackAlong fb.left (Over.w fb) =
      D₁.pullbackAlong b.left (Over.w b) := by
    rw [hDg, RelEffCartierDiv.pullbackAlong_comp]
    exact pullbackAlong_congr_map D₁ hfb _ _
  have hsumA := supported_point_congr c U G q s₁ _ _ hpullA hA
  have hsumB := supported_point_congr c U G q s₁ _ _ hpullB hA₀
  have hpB' := point_difference_congr G (T := T) (inc.left ≫ pB.left)
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s₁.universal s₁.sum
        (Dg.pullbackAlong fa.left (Over.w fa)) hA))
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s₁.universal s₁.sum
        (Dg.pullbackAlong fb.left (Over.w fb)) hA₀))
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s₁.universal s₁.sum
        (D₁.pullbackAlong a.left (Over.w a)) (hpullA ▸ hA)))
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s₁.universal s₁.sum
        (D₁.pullbackAlong b.left (Over.w b)) (hpullB ▸ hA₀))) hpB hsumA hsumB
  have hquotient := supported_difference_blocks_of_degree c U G q hdegree s s₀ s₁
    D D₀ D₁ hmul a.left b.left (Over.w a) (Over.w b) hDa hDb
    (hD₀U.pullbackAlong a.left (Over.w a)) (hpullA ▸ hA)
    (hD₀U.pullbackAlong b.left (Over.w b)) (hpullB ▸ hA₀)
  exact integral_product_of_block_points G inc red traceA traceB genericMap tracePoint pR pB
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong a.left (Over.w a)) hDa))
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong b.left (Over.w b)) hDb))
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s₀.universal s₀.sum (D₀.pullbackAlong a.left (Over.w a))
        (hD₀U.pullbackAlong a.left (Over.w a))) *
      (commGroupPointEquiv G T.hom
        (supportedDivisorSum c U s₀.universal s₀.sum (D₀.pullbackAlong b.left (Over.w b))
          (hD₀U.pullbackAlong b.left (Over.w b))))⁻¹)
    (commGroupPointEquiv G T.hom
      (supportedDivisorSum c U s₁.universal s₁.sum (D₁.pullbackAlong a.left (Over.w a))
        (hpullA ▸ hA)) *
      (commGroupPointEquiv G T.hom
        (supportedDivisorSum c U s₁.universal s₁.sum (D₁.pullbackAlong b.left (Over.w b))
          (hpullB ▸ hA₀)))⁻¹)
    htraceA htraceB hquotient hpR hpB' hpRred hpBred

private def uniformTameIntegralTraceDifference
    {K : Type u} [Field K] [IsAlgClosed K]
    {C : Scheme.{u}} [IsIntegral C] [IsNormalIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (U : C.Opens) (_hU : (U : Set C).Nonempty)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ c))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    (V : G.X.left.Opens) (_hV : IsAffineOpen V)
    (_hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G.X).left ⊆ V) : Prop :=
    let _ : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ [Algebra.EssFiniteType K C.functionField] [AlgebraicCurve.IsCurveOver K C.functionField],
    ∃ t : C.functionField, Transcendental K t ∧
      ∃ Dpole : AlgebraicCurve.Modulus K C.functionField,
    ∀ (B : Scheme.{u}) [IsIntegral B]
      (b : B ⟶ Spec (.of K)) [IsProper b] [SmoothOfRelativeDimension 1 b]
      [GeometricallyIntegral b]
      (π : C ⟶ B) (hπ : π ≫ b = c)
      [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
      (n : ℕ) (hn : ∀ y : B, π.finrank y = n),
    let _ : Algebra K B.functionField := (AlgebraicCurve.baseToFunctionField b).toAlgebra
    ∀ [Algebra B.functionField C.functionField]
      [IsScalarTower K B.functionField C.functionField]
      [FiniteDimensional B.functionField C.functionField]
      [Algebra.IsSeparable B.functionField C.functionField]
      [AlgebraicCurve.IsCurveOver K B.functionField],
    (C.fromSpecStalk (genericPoint C) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap B.functionField C.functionField)) ≫
        B.fromSpecStalk (genericPoint B)) →
    ∀ (p : RatFunc K ≃ₐ[K] B.functionField) (g : C.functionFieldˣ),
      algebraMap B.functionField C.functionField (p RatFunc.X) =
        (g : C.functionField) - 1 →
    ∀ e : ℕ, 0 < e → (e : K) ≠ 0 →
      (∀ w : AlgebraicCurve.Place K C.functionField,
        ((AlgebraicCurve.CurveModel.ofSmoothProperCurve c).placeEquiv.symm w).1 ∉ U →
          w.ord ((g : C.functionField) - 1) = (e : ℤ)) →
      (∀ w : AlgebraicCurve.Place K C.functionField,
        ((AlgebraicCurve.CurveModel.ofSmoothProperCurve c).placeEquiv.symm w).1 ∉ U →
          let cc : ℤ := max 1 (2 * (Dpole w : ℤ))
          cc - min (w.ord t) cc < (e : ℤ)) →
    ∀ w₀ : AlgebraicCurve.Place K C.functionField,
      ((AlgebraicCurve.CurveModel.ofSmoothProperCurve c).placeEquiv.symm w₀).1 ∉ U →
    let W := finiteMapTraceLocus c b π hπ n hn U
    ∃ (hW : (W : Set B).Nonempty)
      (α : B.functionField →ₐ[K] LaurentSeries K)
      (θ : B.functionField →ₐ[K] PowerSeries (LaurentSeries K)),
      α (p RatFunc.X) = HahnSeries.single (e : ℤ) (1 : K) ∧
      (∀ f : B.functionField, (α f).order =
        (e : ℤ) * (w₀.restrict B.functionField).ord f) ∧
      PowerSeries.constantCoeff.comp θ.toRingHom = α.toRingHom ∧
      θ ((p RatFunc.X)⁻¹) = PowerSeries.C (α ((p RatFunc.X)⁻¹)) + PowerSeries.X ∧
      let x := genericOpenPoint b W hW ≫
        commGroupPointEquiv G (W.ι ≫ b) (finiteCurveTrace c b π hπ n hn U ε G q)
      let O := (LaurentSeries.orderPlace (K := K)).toValuationSubring
      ∃ P : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries O)))) ⟶ G.X,
        Spec.map (CommRingCat.ofHom (PowerSeries.map O.subtype)) ≫ P.left =
          ((traceScalarPointMap θ ≫ x) *
            (traceScalarPointMap
              ((IsScalarTower.toAlgHom K (LaurentSeries K)
                (PowerSeries (LaurentSeries K))).comp α) ≫ x)⁻¹).left ∧
        Spec.map (CommRingCat.ofHom (PowerSeries.map (IsLocalRing.residue O))) ≫ P.left =
          (1 : Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap K (PowerSeries (IsLocalRing.ResidueField O))))) ⟶ G.X).left

/-- Uniform exact tame contact at the original boundary makes the formal
difference of the original finite curve trace integral with unit residue.
The source field is the actual function field of the original curve. The
base field is the actual function field of the target curve, and its
rational coordinate is retained through the specified algebra equivalence.
The transparent conclusion `uniformTameIntegralTraceDifference` retains
all these quantified data: it chooses the separating parameter and pole
modulus first, then constructs the integral trace difference for every
finite curve map and every test function with the stated tame contact. -/
theorem exists_finiteCurveTrace_uniform_tame_integral_difference
    {K : Type u} [Field K] [IsAlgClosed K]
    {C : Scheme.{u}} [IsIntegral C] [IsNormalIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ c))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    (V : G.X.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G.X).left ⊆ V) :
    uniformTameIntegralTraceDifference c U hU ε G q V hV hunit := by
  classical
  let algC : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  intro essC curveC
  let genericMap := genericOpenPoint c U hU
  obtain ⟨t, ht, Dpole, hboundary⟩ :=
    exists_completedBoundaryBlock_uniform_integral_difference c U hU genericMap
      (genericOpenPoint_comp c U hU) G q V hV hunit
  refine ⟨t, ht, Dpole, ?_⟩
  intro B intB b properB smoothB geometricB π hπ finiteπ flatπ lfpπ n hn
    algB algBC towerBC finBC sepBC curveB hgeneric p g hparameter e hepos he
    hcontact hlarge w₀ hw₀ W
  let v := w₀.restrict B.functionField
  have hcontact₀ := hcontact w₀ hw₀
  have hparameterOrder : w₀.ord
      (algebraMap B.functionField C.functionField (p RatFunc.X)) = (e : ℤ) := by
    rw [hparameter]
    exact hcontact₀
  obtain ⟨hvs, hram₀⟩ := AlgebraicCurve.Place.rational_contact_ramification
    p w₀ e hepos hparameterOrder
  obtain ⟨E₀, hE₀s, _hE₀order, _hE₀c, _hE₀ic, hE₀val⟩ :=
    v.exists_adicCompletion_algEquiv_laurentSeries_of_deg_eq_one
      (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed v) (p RatFunc.X) hvs
  obtain ⟨Eref, hErefg, hErefc, hEreforder, hErefval⟩ :=
    w₀.exists_adicCompletion_tame_normalized_valuation
      (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed w₀)
      ((g : C.functionField) - 1) e he hcontact₀
  let wref : v.fiber C.functionField := ⟨w₀, w₀.restrict_mem_fiber⟩
  let β := AlgebraicCurve.Place.boundaryCompletedBaseMap v wref Eref
  let i := w₀.regularCompletedEmbedding E₀ Eref
  let jO := w₀.regularCompletedIntegralCoefficients E₀ hE₀val Eref hErefval
  have : IsLocalHom jO.toRingHom :=
    w₀.regularCompletedIntegralCoefficients_isLocalHom E₀ hE₀val Eref hErefval
  let O := (LaurentSeries.orderPlace (K := K)).toValuationSubring
  let inc : O →ₐ[K] LaurentSeries K := { toRingHom := O.subtype, commutes' _ := rfl }
  have hjO : inc.comp jO = LaurentSeries.regularBlockCoefficients i := by
    apply AlgHom.ext
    intro f
    exact w₀.regularCompletedIntegralCoefficients_coe E₀ hE₀val Eref hErefval f
  let τ : v.adicCompletion →ₐ[K] PowerSeries (LaurentSeries K) :=
    (LaurentSeries.regularReciprocalDeformation i).comp E₀.toAlgHom
  have hτ : PowerSeries.constantCoeff.comp τ.toRingHom = β.toRingHom := by
    apply RingHom.ext
    intro f
    change PowerSeries.constantCoeff (LaurentSeries.regularReciprocalDeformation i (E₀ f)) = β f
    calc
      PowerSeries.constantCoeff (LaurentSeries.regularReciprocalDeformation i (E₀ f)) =
          i (E₀ f) :=
        RingHom.congr_fun (LaurentSeries.constantCoeff_comp_regularReciprocalDeformation i)
          (E₀ f)
      _ = β f := by
        change Eref (algebraMap v.adicCompletion w₀.adicCompletion (E₀.symm (E₀ f))) = _
        rw [E₀.symm_apply_apply]
        rfl
  let α := β.comp (IsScalarTower.toAlgHom K B.functionField v.adicCompletion)
  let θ := τ.comp (IsScalarTower.toAlgHom K B.functionField v.adicCompletion)
  have hα : α (p RatFunc.X) = HahnSeries.single (e : ℤ) (1 : K) := by
    change Eref (algebraMap v.adicCompletion w₀.adicCompletion
      (algebraMap B.functionField v.adicCompletion (p RatFunc.X))) = _
    rw [← AlgebraicCurve.Place.adicCompletionComap_algebraMap_algebraMap B.functionField w₀,
      hparameter]
    exact hErefg
  have hαorder (f : B.functionField) :
      (α f).order = (e : ℤ) * v.ord f := by
    change (Eref (algebraMap v.adicCompletion w₀.adicCompletion
      (algebraMap B.functionField v.adicCompletion f))).order = _
    rw [← AlgebraicCurve.Place.adicCompletionComap_algebraMap_algebraMap B.functionField w₀,
      hEreforder, w₀.ord_restrict, hram₀]
  have hθ0 : PowerSeries.constantCoeff.comp θ.toRingHom = α.toRingHom := by
    apply RingHom.ext
    intro f
    exact RingHom.congr_fun hτ (algebraMap B.functionField v.adicCompletion f)
  let z := algebraMap B.functionField v.adicCompletion ((p RatFunc.X)⁻¹)
  have hτz : τ z = PowerSeries.C (β z) + PowerSeries.X := by
    have hEz : E₀ z = (HahnSeries.single 1 1 : LaurentSeries K)⁻¹ := by
      change E₀ (algebraMap B.functionField v.adicCompletion ((p RatFunc.X)⁻¹)) = _
      rw [map_inv₀, map_inv₀, hE₀s]
    have hβz : β z = i ((HahnSeries.single 1 1 : LaurentSeries K)⁻¹) := by
      change Eref (algebraMap v.adicCompletion w₀.adicCompletion z) =
        Eref (algebraMap v.adicCompletion w₀.adicCompletion
          (E₀.symm ((HahnSeries.single 1 1 : LaurentSeries K)⁻¹)))
      rw [← hEz, E₀.symm_apply_apply]
    change LaurentSeries.regularReciprocalDeformation i (E₀ z) = _
    rw [hEz, hβz]
    exact LaurentSeries.regularReciprocalDeformation_reciprocal_parameter i
  have hθz : θ ((p RatFunc.X)⁻¹) = PowerSeries.C (α ((p RatFunc.X)⁻¹)) + PowerSeries.X :=
    hτz
  have hcompletedBlocks := by
    as_aux_lemma =>
      exact exists_finiteCurveTrace_powerSeries_completed_blocks c b π hπ n hn U
        hgeneric v E₀ hE₀val
  obtain ⟨a₀, ha₀base, ha₀generic, V₀, hV₀, hsel, m, k, D₀, D₁,
      hD₀, hD₁, hD₀U, hmul, hdegree, d, hdsource, hdbase⟩ := hcompletedBlocks
  let O₀ := v.powerSeriesEquivCompletionIntegers E₀ hE₀val
  let g₀ := Spec.map (CommRingCat.ofHom
    ((algebraMap v.adicCompletionIntegers v.adicCompletion).comp O₀.toRingHom))
  let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a₀ rfl
  let I := {w : v.fiber C.functionField //
    ((AlgebraicCurve.CurveModel.ofSmoothProperCurve c).placeEquiv.symm w.1).1 ∉ U}
  let _ : Fintype I := Fintype.ofFinite I
  let Dg := D₁.pullbackAlong g₀ (Category.assoc g₀ a₀ b).symm
  have hErefs : Eref (algebraMap C.functionField w₀.adicCompletion
      (algebraMap B.functionField C.functionField (p RatFunc.X))) =
        HahnSeries.single (e : ℤ) (1 : K) := by rw [hparameter]; exact hErefg
  let algL : Algebra v.adicCompletion (LaurentSeries K) := β.toRingHom.toAlgebra
  have hcompletedEmbeddings := by
    as_aux_lemma =>
      exact AlgebraicCurve.Place.exists_common_boundary_completed_embeddings v p hvs g
        hparameter e he wref Eref hErefc hErefs (fun w : I => w.1)
        (fun w => AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed w.1.1)
        (fun w => hcontact w.1.1 w.2)
  obtain ⟨towerEL, towerEF, sepEF, embeddings, hinj, hfinrank, horders, hnormalized⟩ :=
    hcompletedEmbeddings
  let fields (w : I) := w.1.1.adicCompletion
  let jf (w : I) : C.functionField →ₐ[K] fields w :=
    IsScalarTower.toAlgHom K C.functionField (fields w)
  let sourceBoundaryTower : IsScalarTower K v.adicCompletion (LaurentSeries K) := towerEL
  let τ₀ : v.adicCompletion →ₐ[K] PowerSeries (LaurentSeries K) :=
    completedBoundaryConstantMap (K := K) (E := v.adicCompletion)
      (tower := sourceBoundaryTower)
  let tL := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (LaurentSeries K))))
  let γ := formalBlockCoefficientMap (LaurentSeries.regularBlockCoefficients i)
  let fa := γ ≫ formalBlockBaseMap (PowerSeries.reciprocalParameterDeformation (K := K))
  let fb := γ ≫ formalBlockBaseMap (formalBlockConstantInclusion (K := K))
  let idr : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))) ⟶
      Over.mk (a₀ ≫ b) := Over.homMk (𝟙 _) ((Category.id_comp _).trans ha₀base)
  let a := fa ≫ idr
  let b' := fb ≫ idr
  have hfa : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ g₀ = a.left := by
    rw [regular_base_map_comparison]
    exact (Category.comp_id _).symm
  have hfb : Spec.map (CommRingCat.ofHom τ₀.toRingHom) ≫ g₀ = b'.left := by
    have hβ : i.comp E₀.toAlgHom =
        IsScalarTower.toAlgHom K v.adicCompletion (LaurentSeries K) := by
      apply AlgHom.ext
      intro f
      change Eref (algebraMap v.adicCompletion w₀.adicCompletion (E₀.symm (E₀ f))) = _
      rw [E₀.symm_apply_apply]
      rfl
    have h := constant_base_map_comparison v E₀ hE₀val i
    rw [hβ] at h
    exact h.trans (Category.comp_id _).symm
  have hτstructure : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ ((g₀ ≫ a₀) ≫ b) = tL := by
    rw [← Category.assoc, ← Category.assoc, hfa, Category.assoc]
    exact Over.w a
  have hτ₀structure : Spec.map (CommRingCat.ofHom τ₀.toRingHom) ≫ ((g₀ ≫ a₀) ≫ b) = tL := by
    rw [← Category.assoc, ← Category.assoc, hfb, Category.assoc]
    exact Over.w b'
  have hbase : d.hom ≫ Dg.I.subschemeι ≫ pullback.snd c ((g₀ ≫ a₀) ≫ b) =
      Sigma.desc (fun w : I => Spec.map (CommRingCat.ofHom
        (algebraMap v.adicCompletion (fields w)))) := by
    as_aux_lemma =>
      apply Sigma.hom_ext
      intro w
      rw [Sigma.ι_comp_desc]
      exact hdbase w
  let s₀ := chooseOpenCurveSum c U (commGroupRelativeLaw G) q m
    (commGroupRelativeLaw_isCommutative G) ε
  let s₁ := chooseOpenCurveSum c U (commGroupRelativeLaw G) q k
    (commGroupRelativeLaw_isCommutative G) ε
  have hboundaryPoint := by
    as_aux_lemma =>
      exact (@hboundary v.adicCompletion inferInstance inferInstance algL
        sourceBoundaryTower) k _ Dg
        I fields (fun _ => e) hfinrank embeddings hinj jf d hbase hdsource s₁ τ hτ
        hτstructure hτ₀structure (fun w : I => w.1.1) horders g e hepos he
        (fun w => hcontact w.1.1 w.2) hnormalized (fun w => hlarge w.1.1 w.2)
        z (by
          intro w
          change algebraMap C.functionField (fields w) (((g : C.functionField) - 1)⁻¹) = _
          rw [← hparameter, ← map_inv₀,
            ← IsScalarTower.algebraMap_apply B.functionField C.functionField (fields w),
            IsScalarTower.algebraMap_apply B.functionField v.adicCompletion (fields w)]) hτz
  obtain ⟨hA, hA₀, pB, hpB, hpBred⟩ := hboundaryPoint
  obtain ⟨pR, hpR, hpRred⟩ := exists_regularCartierBlock_integral_difference
    jO inc c U G q s₀ (a₀ ≫ b) ha₀base D₀ hD₀U
  rw [hjO] at hpR
  have hW : (W : Set B).Nonempty := finiteMapTraceLocus_nonempty c b π hπ n hn U hU
  let ηB := genericOpenPoint b W hW
  have hηB : ηB.left ≫ W.ι = B.fromSpecStalk (genericPoint B) :=
    genericOpenPoint_comp b W hW
  let aW := traceScalarPointMap θ ≫ ηB
  let bW := traceScalarPointMap
    ((IsScalarTower.toAlgHom K (LaurentSeries K) (PowerSeries (LaurentSeries K))).comp α) ≫ ηB
  have htriangleA : a.left ≫ a₀ = aW.left ≫ W.ι := by
    rw [← hfa, Category.assoc, ha₀generic]
    change _ = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ ηB.left ≫ W.ι
    rw [hηB, ← Category.assoc, ← Spec.map_comp]
    rfl
  have htriangleB : b'.left ≫ a₀ = bW.left ≫ W.ι := by
    rw [← hfb, Category.assoc, ha₀generic]
    change _ = Spec.map (CommRingCat.ofHom
      ((IsScalarTower.toAlgHom K (LaurentSeries K)
        (PowerSeries (LaurentSeries K))).comp α).toRingHom) ≫ ηB.left ≫ W.ι
    rw [hηB, ← Category.assoc, ← Spec.map_comp]
    rfl
  obtain ⟨hDa, htraceA⟩ := finiteCurveTrace_point_eq_integral_graph_sum c b π hπ n hn U
    ε G q a₀ rfl a.left (Over.w a) aW htriangleA
  obtain ⟨hDb, htraceB⟩ := finiteCurveTrace_point_eq_integral_graph_sum c b π hπ n hn U
    ε G q a₀ rfl b'.left (Over.w b') bW htriangleB
  let s := chooseOpenCurveSum c U (commGroupRelativeLaw G) q n
    (commGroupRelativeLaw_isCommutative G) ε
  let gOver : Over.mk ((g₀ ≫ a₀) ≫ b) ⟶ Over.mk (a₀ ≫ b) :=
    Over.homMk g₀ (Category.assoc g₀ a₀ b).symm
  let faOver : Over.mk tL ⟶ Over.mk ((g₀ ≫ a₀) ≫ b) :=
    Over.homMk (Spec.map (CommRingCat.ofHom τ.toRingHom)) hτstructure
  let fbOver : Over.mk tL ⟶ Over.mk ((g₀ ≫ a₀) ≫ b) :=
    Over.homMk (Spec.map (CommRingCat.ofHom τ₀.toRingHom)) hτ₀structure
  let tO := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries O)))
  let tRed := Spec.map (CommRingCat.ofHom
    (algebraMap K (PowerSeries (IsLocalRing.ResidueField O))))
  let fInc : Over.mk tL ⟶ Over.mk tO :=
    Over.homMk (Spec.map (CommRingCat.ofHom (PowerSeries.map O.subtype))) (by
      change Spec.map (CommRingCat.ofHom (PowerSeries.map O.subtype)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries O))) =
          Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (LaurentSeries K))))
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (PowerSeries.mapAlgHom inc).comp_algebraMap))
  let red : O →ₐ[K] IsLocalRing.ResidueField O := IsScalarTower.toAlgHom K O _
  let fRed : Over.mk tRed ⟶ Over.mk tO :=
    Over.homMk (Spec.map (CommRingCat.ofHom (PowerSeries.map (IsLocalRing.residue O)))) (by
      change Spec.map (CommRingCat.ofHom (PowerSeries.map (IsLocalRing.residue O))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries O))) =
          Spec.map (CommRingCat.ofHom
            (algebraMap K (PowerSeries (IsLocalRing.ResidueField O))))
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (PowerSeries.mapAlgHom red).comp_algebraMap))
  let P := pR * pB
  have hfinal := integral_trace_difference_of_completed_blocks c U G q
    (R := Over.mk (a₀ ≫ b)) (E := Over.mk ((g₀ ≫ a₀) ≫ b))
    (O := Over.mk tO) (T := Over.mk tL) (Tred := Over.mk tRed)
    (F := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B.functionField))))
    (W := Over.mk (W.ι ≫ b)) hdegree s s₀ s₁
    D D₀ D₁ hmul hD₀U gOver Dg rfl faOver fbOver a b' hfa hfb hA hA₀
    fInc fRed pR pB hpR hpB hpRred hpBred
    (traceScalarPointMap θ)
    (traceScalarPointMap
      ((IsScalarTower.toAlgHom K (LaurentSeries K) (PowerSeries (LaurentSeries K))).comp α))
    ηB (commGroupPointEquiv G (W.ι ≫ b) (finiteCurveTrace c b π hπ n hn U ε G q))
    hDa hDb htraceA htraceB
  exact ⟨hW, α, θ, hα, hαorder, hθ0, hθz, P, hfinal.1, hfinal.2⟩

end AlgebraicGeometry.GeneralizedJacobian
