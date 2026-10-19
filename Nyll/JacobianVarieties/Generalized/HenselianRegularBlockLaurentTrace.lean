/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.HenselianRegularBlockTrace
import Nyll.JacobianVarieties.Generalized.FiniteCurveTrace
import Nyll.JacobianVarieties.Albanese.SupportedDivisorSumAdditivity
import Nyll.AlgebraicCurves.Places.Degree.LaurentCompletionIntegersDegEqOne

/-! # The regular block on the common Laurent coefficient field

The actual integral divisor is transported through a native K-algebra
isomorphism of its base with K[[s]]. Its actual Henselian regular block
supplies an integral group point reducing to one. On extending coefficients,
that point is exactly the quotient of the two pulled-back regular-block
sums. Separately, the corresponding full graph-divisor sums are identified
with the original finiteCurveTrace by divisor pullback composition and
sum naturality. These equalities retain the full Cartier ideals and can be
combined with supportedDivisorSum_mul and the boundary-block comparison.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj nonZeroDivisors

namespace JacobianVarieties.Albanese

private def scalarPointMap {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext f.comp_algebraMap))

/-- Coefficient extension of an actual integral formal group point. -/
def formalBlockCoefficientMap
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (j : PowerSeries K →ₐ[K] L) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (PowerSeries K))))) :=
  scalarPointMap (PowerSeries.mapAlgHom j)

/-- The actual generic regular-block point is the quotient of its two
full pulled-back divisor sums. The coefficient field can be any common
extension field used to split the tame boundary components. -/
theorem regularBlockDifference_generic_two_sums
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (U : C.Opens)
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {m : ℕ}
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q m)
    (D₀ : RelEffCartierDiv c m
      (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))))
    (hD₀ : D₀.SupportedIn U) (j : PowerSeries K →ₐ[K] L) :
    let t := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))
    let tL := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))
    let γ := formalBlockCoefficientMap j
    let α := formalBlockBaseMap (PowerSeries.reciprocalParameterDeformation (K := K))
    let β := formalBlockBaseMap (formalBlockConstantInclusion (K := K))
    let x := commGroupPointEquiv G t
      (supportedDivisorSum c U s.universal s.sum D₀ hD₀)
    γ ≫ RegularBlockFormalDeformation.difference x =
      commGroupPointEquiv G tL
          (supportedDivisorSum c U s.universal s.sum
            (D₀.pullbackAlong (γ ≫ α).left (Over.w (γ ≫ α)))
            (hD₀.pullbackAlong (γ ≫ α).left (Over.w (γ ≫ α)))) *
        (commGroupPointEquiv G tL
          (supportedDivisorSum c U s.universal s.sum
            (D₀.pullbackAlong (γ ≫ β).left (Over.w (γ ≫ β)))
            (hD₀.pullbackAlong (γ ≫ β).left (Over.w (γ ≫ β)))))⁻¹ := by
  intro t tL γ α β x
  rw [supportedDivisorSum_point_naturality c U G q s,
    supportedDivisorSum_point_naturality c U G q s]
  change γ ≫ ((α ≫ x) * (β ≫ x)⁻¹) =
    ((γ ≫ α) ≫ x) * ((γ ≫ β) ≫ x)⁻¹
  rw [MonObj.comp_mul, GrpObj.comp_inv]
  simp only [Category.assoc]

/-- Transport a genuine integral family through its actual K-algebra base
isomorphism and construct its regular-block point. Both generic sums are
computed over every common coefficient field, and the original closed-fibre
selection, complementary full ideal, degree and unit reduction are retained. -/
theorem exists_transported_regularBlock_integral_difference
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (U : C.Opens)
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ c))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    (O : PowerSeries K ≃ₐ[K] R) {n : ℕ}
    (D : RelEffCartierDiv c n (Spec.map (CommRingCat.ofHom (algebraMap K R)))) :
    let t := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))
    let fO := scalarPointMap O.symm.toAlgHom
    let DP := D.pullbackAlong fO.left (Over.w fO)
    let p := DP.I.subschemeι ≫ pullback.snd c t
    let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries K)))
    ∃ (V : DP.I.subscheme.Opens) (hV : IsClosed (V : Set DP.I.subscheme)),
      let W : DP.I.subscheme.Opens := ⟨(V : Set DP.I.subscheme)ᶜ, hV.isOpen_compl⟩
      (pullback.fst p r ⁻¹' (V : Set DP.I.subscheme) =
        (pullback.fst p r ≫ DP.I.subschemeι ≫ pullback.fst c t) ⁻¹' (U : Set C)) ∧
      ∃ (m k : ℕ) (D₀ : RelEffCartierDiv c m t) (D₁ : RelEffCartierDiv c k t)
        (hD₀ : D₀.SupportedIn U) (s : OpenCurveSum c U (commGroupRelativeLaw G) q m),
        D₀.I = (V.ι ≫ DP.I.subschemeι).ker ∧
        D₁.I = (W.ι ≫ DP.I.subschemeι).ker ∧
        DP.I = D₀.I * D₁.I ∧ n = m + k ∧
        let x := commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum D₀ hD₀)
        Spec.map (CommRingCat.ofHom (PowerSeries.map (PowerSeries.constantCoeff (R := K)))) ≫
          (RegularBlockFormalDeformation.difference x).left = (1 : Over.mk t ⟶ G.X).left ∧
        ∀ (L : Type u) [Field L] [Algebra K L] (j : PowerSeries K →ₐ[K] L),
          let tL := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))
          let γ := formalBlockCoefficientMap j
          let α := formalBlockBaseMap (PowerSeries.reciprocalParameterDeformation (K := K))
          let β := formalBlockBaseMap (formalBlockConstantInclusion (K := K))
          γ ≫ RegularBlockFormalDeformation.difference x =
            commGroupPointEquiv G tL
                (supportedDivisorSum c U s.universal s.sum
                  (D₀.pullbackAlong (γ ≫ α).left (Over.w (γ ≫ α)))
                  (hD₀.pullbackAlong (γ ≫ α).left (Over.w (γ ≫ α)))) *
              (commGroupPointEquiv G tL
                (supportedDivisorSum c U s.universal s.sum
                  (D₀.pullbackAlong (γ ≫ β).left (Over.w (γ ≫ β)))
                  (hD₀.pullbackAlong (γ ≫ β).left (Over.w (γ ≫ β)))))⁻¹ := by
  intro t fO DP p r
  obtain ⟨V, hV, hsel, m, k, D₀, D₁, hD₀, s, hI₀, hI₁, hmul, hdegree, hred⟩ :=
    exists_henselian_regularBlock_integral_trace c U ε G q DP
  refine ⟨V, hV, hsel, m, k, D₀, D₁, hD₀, s, hI₀, hI₁, hmul, hdegree, hred, ?_⟩
  intro L fieldL algebraKL j
  exact regularBlockDifference_generic_two_sums c U G q s D₀ hD₀ j

end JacobianVarieties.Albanese

namespace AlgebraicGeometry.GeneralizedJacobian

open JacobianVarieties.Albanese

private theorem pullbackAlong_commuting_triangle
    {S C B V R T : Scheme.{u}} {c : C ⟶ S} {b : B ⟶ S}
    {r : R ⟶ S} {t : T ⟶ S} {n : ℕ}
    (D : RelEffCartierDiv c n b) (v : V ⟶ B)
    (a₀ : R ⟶ B) (ha₀ : a₀ ≫ b = r) (f : T ⟶ R) (hf : f ≫ r = t)
    (a : Over.mk t ⟶ Over.mk (v ≫ b)) (htriangle : f ≫ a₀ = a.left ≫ v) :
    (D.pullbackAlong v rfl).pullbackAlong a.left (Over.w a) =
      (D.pullbackAlong a₀ ha₀).pullbackAlong f hf := by
  rw [RelEffCartierDiv.pullbackAlong_comp, RelEffCartierDiv.pullbackAlong_comp]
  congr 1
  exact htriangle.symm

private theorem supportedDivisorSum_point_eq_of_pullback_eq
    {K : Type u} [Field K] {C V T : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (U : C.Opens)
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {n : ℕ}
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q n)
    {v : V ⟶ Spec (.of K)} {t : T ⟶ Spec (.of K)}
    (A : RelEffCartierDiv c n v) (hA : A.SupportedIn U)
    (a : Over.mk t ⟶ Over.mk v) (D : RelEffCartierDiv c n t)
    (hfamilies : A.pullbackAlong a.left (Over.w a) = D) :
    ∃ hD : D.SupportedIn U,
      a ≫ commGroupPointEquiv G v
          (supportedDivisorSum c U s.universal s.sum A hA) =
        commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum D hD) := by
  subst D
  refine ⟨hA.pullbackAlong a.left (Over.w a), ?_⟩
  simpa only [Over.homMk_eta] using
    (supportedDivisorSum_point_naturality c U G q s
      (t := v) (t' := t) A hA a.left (Over.w a)).symm

/-- Pulling the original finiteCurveTrace to a test scheme is exactly the
sum of the original graph divisor pulled through the actual integral base
map. The commuting triangle is a diagram of base maps, not a supplied
comparison of traces or divisors. -/
theorem finiteCurveTrace_point_eq_integral_graph_sum
    {K : Type u} [Field K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (b : B ⟶ Spec (.of K)) [IsSeparated b]
    (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : C.Opens)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ c))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    {R T : Scheme.{u}} {r : R ⟶ Spec (.of K)} {t : T ⟶ Spec (.of K)}
    (a₀ : R ⟶ B) (ha₀ : a₀ ≫ b = r) (f : T ⟶ R) (hf : f ≫ r = t) :
    let V := finiteMapTraceLocus c b π hπ n hn U
    let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a₀ ha₀
    let s := chooseOpenCurveSum c U (commGroupRelativeLaw G) q n
      (commGroupRelativeLaw_isCommutative G) ε
    ∀ (a : Over.mk t ⟶ Over.mk (V.ι ≫ b)), f ≫ a₀ = a.left ≫ V.ι →
    ∃ hD : (D.pullbackAlong f hf).SupportedIn U,
      a ≫ commGroupPointEquiv G (V.ι ≫ b) (finiteCurveTrace c b π hπ n hn U ε G q) =
        commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong f hf) hD) := by
  intro V D s a htriangle
  let A := finiteMapTraceFamily c b π hπ n hn U
  have hA := finiteMapTraceFamily_supported c b π hπ n hn U
  have hfamilies : A.pullbackAlong a.left (Over.w a) = D.pullbackAlong f hf :=
    pullbackAlong_commuting_triangle (finiteMapFiberDivisor c b π hπ n hn)
      V.ι a₀ ha₀ f hf a htriangle
  change ∃ hD : (D.pullbackAlong f hf).SupportedIn U,
    a ≫ commGroupPointEquiv G (V.ι ≫ b)
        (supportedDivisorSum c U s.universal s.sum A hA) =
      commGroupPointEquiv G t
        (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong f hf) hD)
  exact supportedDivisorSum_point_eq_of_pullback_eq c U G q s A hA a
    (D.pullbackAlong f hf) hfamilies

end AlgebraicGeometry.GeneralizedJacobian
