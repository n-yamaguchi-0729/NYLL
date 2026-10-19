/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.HenselianRegularBlockLaurentTrace
import Nyll.SchemeTheory.GroupSchemes.RegularBlockIntegralCoefficients

/-! # The actual regular Cartier block over the common integral coefficients

The original structural map of the integral graph is retained. Its proved
equality with the canonical scalar map is used only by an identity morphism
in the over category. In particular, no Cartier ideal or Henselian selected
block is rebuilt when extending its actual divisor-sum difference to the
common valuation ring.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace JacobianVarieties.Albanese

/-- An actual supported regular block gives an integral difference over
every local coefficient extension. Its generic value is the quotient of
the two actual pulled-back sums, with the original base map retained. -/
theorem exists_regularCartierBlock_integral_difference
    {K R L : Type u} [Field K] [CommRing R] [IsLocalRing R] [Field L]
    [Algebra K R] [Algebra K L]
    (j : PowerSeries K →ₐ[K] R) [IsLocalHom j.toRingHom]
    (k : R →ₐ[K] L)
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (U : C.Opens)
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {m : ℕ}
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q m)
    (r : Spec (.of (PowerSeries K)) ⟶ Spec (.of K))
    (hr : r = Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))))
    (D : RelEffCartierDiv c m r) (hD : D.SupportedIn U) :
    let t := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K)))
    let tL := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))
    let h : Over.mk t ⟶ Over.mk r :=
      Over.homMk (𝟙 _) ((Category.id_comp r).trans hr)
    let γ := formalBlockCoefficientMap (k.comp j)
    let α := formalBlockBaseMap (PowerSeries.reciprocalParameterDeformation (K := K))
    let β := formalBlockBaseMap (formalBlockConstantInclusion (K := K))
    let a := (γ ≫ α) ≫ h
    let b := (γ ≫ β) ≫ h
    ∃ p : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries R)))) ⟶ G.X,
      Spec.map (CommRingCat.ofHom (PowerSeries.map k.toRingHom)) ≫ p.left =
        (commGroupPointEquiv G tL
            (supportedDivisorSum c U s.universal s.sum
              (D.pullbackAlong a.left (Over.w a))
              (hD.pullbackAlong a.left (Over.w a))) *
          (commGroupPointEquiv G tL
            (supportedDivisorSum c U s.universal s.sum
              (D.pullbackAlong b.left (Over.w b))
              (hD.pullbackAlong b.left (Over.w b))))⁻¹).left ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.map (IsLocalRing.residue R))) ≫ p.left =
        (1 : Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap K (PowerSeries (IsLocalRing.ResidueField R))))) ⟶ G.X).left := by
  intro t tL h γ α β a b
  let y := commGroupPointEquiv G r
    (supportedDivisorSum c U s.universal s.sum D hD)
  let x := h ≫ y
  let p := RegularBlockFormalDeformation.integralCoefficientDifference j x
  have hgeneric := RegularBlockFormalDeformation.integralCoefficientDifference_generic j k x
  have hsum : γ ≫ RegularBlockFormalDeformation.difference x =
      commGroupPointEquiv G tL
          (supportedDivisorSum c U s.universal s.sum
            (D.pullbackAlong a.left (Over.w a))
            (hD.pullbackAlong a.left (Over.w a))) *
        (commGroupPointEquiv G tL
          (supportedDivisorSum c U s.universal s.sum
            (D.pullbackAlong b.left (Over.w b))
            (hD.pullbackAlong b.left (Over.w b))))⁻¹ := by
    rw [supportedDivisorSum_point_naturality c U G q s,
      supportedDivisorSum_point_naturality c U G q s]
    change γ ≫ ((α ≫ (h ≫ y)) * (β ≫ (h ≫ y))⁻¹) =
      (((γ ≫ α) ≫ h) ≫ y) * (((γ ≫ β) ≫ h) ≫ y)⁻¹
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    simp only [Category.assoc]
  refine ⟨p, hgeneric.trans ?_,
    RegularBlockFormalDeformation.integralCoefficientDifference_residue j x⟩
  exact congrArg (fun f : Over.mk tL ⟶ G.X => f.left) hsum

end JacobianVarieties.Albanese
