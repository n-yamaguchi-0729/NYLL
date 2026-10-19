/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Support.ClopenDivisorDecomposition
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.JacobianVarieties.Albanese.OpenCurveSumChoice
import Nyll.SchemeTheory.GroupSchemes.RegularBlockFormalDeformation
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Integral trace differences of the actual regular Henselian block

The closed-fibre part supported in the source open lifts to an actual
finite-flat divisor block and a complementary block. The represented
divisor sum constructs its point in the original group over `K[[s]]`.
Arbitrary base-change naturality identifies the deformed and constant
pullbacks with the sums of the actual pulled-back divisors. Their difference
is a point over `K[[s]][[T]]` reducing to the identity modulo `s`.
The construction retains full ideals, multiplicities, and the original
group target; no splitting, separability, or tameness is used.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace JacobianVarieties.Albanese

variable {K : Type u} [Field K]

private theorem powerSeries_henselianLocalRing : HenselianLocalRing (PowerSeries K) where
  is_henselian P hP a ha hunit := by
    rw [PowerSeries.maximalIdeal_eq_span_X] at ha ⊢
    exact HenselianRing.is_henselian (I := Ideal.span {(PowerSeries.X : PowerSeries K)})
      P hP a ha (hunit.map (Ideal.Quotient.mk _))

/-- Actual group points of a represented divisor sum retain arbitrary
base-change naturality, through the original point equivalence. -/
theorem supportedDivisorSum_point_naturality
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (U : C.Opens)
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {n : ℕ}
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q n)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (.of K)} {t' : T' ⟶ Spec (.of K)}
    (D : RelEffCartierDiv c n t) (hD : D.SupportedIn U)
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    commGroupPointEquiv G t'
        (supportedDivisorSum c U s.universal s.sum
          (D.pullbackAlong f hf) (hD.pullbackAlong f hf)) =
      (Over.homMk f hf : Over.mk t' ⟶ Over.mk t) ≫
        commGroupPointEquiv G t (supportedDivisorSum c U s.universal s.sum D hD) := by
  rw [← supportedDivisorSum_naturality]
  exact commGroupPointEquiv_comp G t t' ⟨f, hf⟩ _

/-- The actual over-scheme map induced by any deformation of `K[[s]]`
with coefficients in `K[[s]][[T]]`. -/
def formalBlockBaseMap
    (f : PowerSeries K →ₐ[K] PowerSeries (PowerSeries K)) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (PowerSeries K))))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))) =
        Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (PowerSeries K))))
    rw [← Spec.map_comp]
    apply congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of (PowerSeries (PowerSeries K)) =>
      Spec.map h)
    exact CommRingCat.hom_ext f.comp_algebraMap)

/-- Constant inclusion of the coefficient ring, used for the undeformed
pullback of a regular finite-flat block. -/
def formalBlockConstantInclusion :
    PowerSeries K →ₐ[K] PowerSeries (PowerSeries K) where
  toRingHom := PowerSeries.C
  commutes' a := (PowerSeries.algebraMap_apply (r := a)).symm

/-- The integral difference is exactly the quotient of the actual sums
of the reciprocal and constant pulled-back divisors. -/
theorem supportedDivisorSum_reciprocal_difference
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (U : C.Opens)
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {n : ℕ}
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q n)
    (D : RelEffCartierDiv c n
      (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))))
    (hD : D.SupportedIn U) :
    let t := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))
    let t' := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (PowerSeries K))))
    let α := formalBlockBaseMap (PowerSeries.reciprocalParameterDeformation (K := K))
    let β := formalBlockBaseMap (formalBlockConstantInclusion (K := K))
    RegularBlockFormalDeformation.difference
        (commGroupPointEquiv G t (supportedDivisorSum c U s.universal s.sum D hD)) =
      commGroupPointEquiv G t'
          (supportedDivisorSum c U s.universal s.sum
            (D.pullbackAlong α.left (Over.w α)) (hD.pullbackAlong α.left (Over.w α))) *
        (commGroupPointEquiv G t'
          (supportedDivisorSum c U s.universal s.sum
            (D.pullbackAlong β.left (Over.w β)) (hD.pullbackAlong β.left (Over.w β))))⁻¹ := by
  intro t t' α β
  rw [supportedDivisorSum_point_naturality c U G q s,
    supportedDivisorSum_point_naturality c U G q s]
  rfl

/-- The actual regular block has its actual integral group sum and formal
difference with unit residue. The complementary block, full product ideal,
degree equality, and exact closed-fibre selection are retained for total
trace decomposition. The sum map is constructed from the existing divisor
representer and the specified genuine point of the source open. -/
theorem exists_henselian_regularBlock_integral_trace
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (U : C.Opens)
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ c))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {n : ℕ}
    (D : RelEffCartierDiv c n
      (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))))) :
    let t := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))
    let p := D.I.subschemeι ≫ pullback.snd c t
    let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries K)))
    ∃ (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme)),
      let W : D.I.subscheme.Opens := ⟨(V : Set D.I.subscheme)ᶜ, hV.isOpen_compl⟩
      (pullback.fst p r ⁻¹' (V : Set D.I.subscheme) =
        (pullback.fst p r ≫ D.I.subschemeι ≫ pullback.fst c t) ⁻¹' (U : Set C)) ∧
      ∃ (m k : ℕ) (D₀ : RelEffCartierDiv c m t) (D₁ : RelEffCartierDiv c k t)
        (hD₀ : D₀.SupportedIn U) (s : OpenCurveSum c U (commGroupRelativeLaw G) q m),
        D₀.I = (V.ι ≫ D.I.subschemeι).ker ∧
        D₁.I = (W.ι ≫ D.I.subschemeι).ker ∧
        D.I = D₀.I * D₁.I ∧ n = m + k ∧
        let x := commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum D₀ hD₀)
        Spec.map (CommRingCat.ofHom
          (PowerSeries.map (PowerSeries.constantCoeff (R := K)))) ≫
            (RegularBlockFormalDeformation.difference x).left =
          (1 : Over.mk t ⟶ G.X).left := by
  intro t p r
  have : HenselianLocalRing (PowerSeries K) := powerSeries_henselianLocalRing
  obtain ⟨V, hV, hVr, m, k, D₀, D₁, hD₀, hD₁, hD₀U, hmul, hdegree⟩ :=
    RelEffCartierDiv.exists_henselian_regularBlock_decomposition D U
  let s := chooseOpenCurveSum c U (commGroupRelativeLaw G) q m
    (commGroupRelativeLaw_isCommutative G) ε
  refine ⟨V, hV, hVr, m, k, D₀, D₁, hD₀U, s, hD₀, hD₁, hmul, hdegree, ?_⟩
  exact RegularBlockFormalDeformation.difference_residue _

end JacobianVarieties.Albanese
