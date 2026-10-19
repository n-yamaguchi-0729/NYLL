/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeneralGroupRegularMapModulus
import Nyll.JacobianVarieties.Generalized.GroundModulusPowerDomination
import Nyll.JacobianVarieties.Generalized.GeometricModulusAlgebraicClosure
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapRestriction

/-! # A full geometric modulus over the original field

An actual boundary Cartier divisor is constructed over the original field.
Over one algebraic closure, the general commutative-group calculation gives
a modulus supported on exactly that boundary. One positive ground-field
power dominates all its multiplicities. Actual divisor restriction and
scalar-extension comparisons then give the full geometric condition for
that same divisor over every algebraically closed extension.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem relativeIdeal_eq_comap_curveIdeal
    {K : Type u} [Field K] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of K)} {d : ℕ}
    (D : RelEffCartierDiv c d (𝟙 (Spec (.of K)))) :
    D.I = (modulusCurveIdeal D).comap (pullback.fst c (𝟙 (Spec (.of K)))) := by
  rw [modulusCurveIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp,
    IsIso.hom_inv_id, Scheme.IdealSheafData.comap_id]

private theorem relativeIdeal_le_of_curveIdeal_power
    {K : Type u} [Field K] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of K)} {d e : ℕ}
    (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (P : RelEffCartierDiv c e (𝟙 (Spec (.of K))))
    (N : ℕ) (hN : 0 < N) (hP : modulusCurveIdeal P = (modulusCurveIdeal D) ^ N) :
    P.I ≤ D.I := by
  rw [relativeIdeal_eq_comap_curveIdeal P, relativeIdeal_eq_comap_curveIdeal D]
  apply Scheme.IdealSheafData.comap_mono
  rw [hP]
  intro W
  change ((modulusCurveIdeal D).ideal W) ^ N ≤ (modulusCurveIdeal D).ideal W
  exact Ideal.pow_le_self (Nat.ne_of_gt hN)

/-- Every actual regular map from a nonempty open smooth proper geometrically
integral curve to a separated commutative group locally of finite type has
one full geometric Cartier modulus over the original field. Its complement
is exactly the original open domain. Neither perfection nor a rational
point on the curve is assumed. -/
theorem exists_group_geometricRegularMapHasModulus
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (q : Over.mk (U.ι ≫ c) ⟶ G.X) :
    ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
      (hDU : modulusComplement (modulusCurveMap D) = U),
      geometricRegularMapHasModulus c D G
        ((Over.homMk (V := Over.mk (U.ι ≫ c)) (C.homOfLE hDU.le)
          (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])) ≫ q) := by
  classical
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  obtain ⟨d₀, D₀, hD₀U⟩ := exists_modulusComplement_eq c U hU
  let r₀ : Over.mk ((modulusComplement (modulusCurveMap D₀)).ι ≫ c) ⟶
      Over.mk (U.ι ≫ c) :=
    Over.homMk (C.homOfLE hD₀U.le)
      (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])
  let q₀ := r₀ ≫ q
  let L := AlgebraicClosure K
  let cL := baseChange K c L
  let D₀L := D₀.changeBaseOfIdentity (specMap K L)
  let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
  let U₀L := modulusComplement (modulusCurveMap D₀L)
  let q₀L := modulusGroupMapScalarExtension c D₀ L G q₀
  have : IsSeparated G_L.X.hom := by
    change IsSeparated (pullback.snd G.X.hom (specMap K L))
    infer_instance
  have : LocallyOfFiniteType G_L.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom (specMap K L))
    infer_instance
  have hU₀L : (U₀L : Set (pullback c (specMap K L) : Scheme.{u})).Nonempty := by
    obtain ⟨x⟩ := modulusComplement_nonempty cL D₀L
    exact ⟨x.1, x.2⟩
  let _ : Algebra L (pullback c (specMap K L)).functionField :=
    (baseToFunctionField cL).toAlgebra
  let ML := CurveModel.ofSmoothProperCurve cL
  obtain ⟨E, hEboundary, hE⟩ := exists_group_regularMap_modulus cL U₀L hU₀L G_L
    ⟨q₀L.left, Over.w q₀L⟩
  have hEsupport : ∀ w, ML.cartierModulus (modulusCurveIdeal D₀L)
      (modulusCurveIdeal_isInvertible D₀L) w = 0 → E w = 0 := by
    intro w hw
    apply (hEboundary w).mpr
    exact (ML.cartierModulus_eq_zero_iff (modulusCurveIdeal D₀L)
      (modulusCurveIdeal_isInvertible D₀L) w).mp hw
  obtain ⟨N, hN, d, D, hpower, hcomplement, hdom⟩ :=
    exists_groundModulus_power_dominating c D₀ L E hEsupport
  have hDD₀ : D.I ≤ D₀.I := relativeIdeal_le_of_curveIdeal_power D₀ D N hN hpower
  let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hDD₀)
    (modulusIdealInclusion_curve c D D₀ hDD₀)
  let qD := r ≫ q₀
  let DL := D.changeBaseOfIdentity (specMap K L)
  let qDL := modulusGroupMapScalarExtension c D L G qD
  have hcomplementL : modulusComplement (modulusCurveMap DL) = U₀L := by
    exact (modulusComplement_scalarExtension c D L).trans
      ((congrArg (fun V : C.Opens => pullback.fst c (specMap K L) ⁻¹ᵁ V)
        hcomplement).trans (modulusComplement_scalarExtension c D₀ L).symm)
  let rL : Over.mk ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) ⟶
      Over.mk (U₀L.ι ≫ cL) :=
    Over.homMk ((pullback c (specMap K L)).homOfLE hcomplementL.le)
      (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])
  let rL' := modulusComplementRestriction cL
    (divisorRestrictionScalarMap D D₀ (Scheme.IdealSheafData.inclusion hDD₀)
      (modulusIdealInclusion_curve c D D₀ hDD₀) L)
    (divisorRestrictionScalarMap_square D D₀ (Scheme.IdealSheafData.inclusion hDD₀)
      (modulusIdealInclusion_curve c D D₀ hDD₀) L)
  have hrL : rL' = rL := by
    apply Over.OverMorphism.ext
    apply (cancel_mono U₀L.ι).mp
    dsimp only [rL', rL, modulusComplementRestriction, Over.homMk_left]
  have hqL : qDL = rL ≫ q₀L := by
    have h := modulusMapScalarExtension_restriction c D L D₀
      (Scheme.IdealSheafData.inclusion hDD₀)
      (modulusIdealInclusion_curve c D D₀ hDD₀) G.X q₀
    change qDL = rL' ≫ q₀L at h
    exact h.trans (congrArg (fun a => a ≫ q₀L) hrL)
  have hDL : ML.regularMapHasModulus DL G_L ⟨qDL.left, Over.w qDL⟩ := by
    have hmod := ML.regularMapHasModulus_restriction_of_values U₀L G_L
      ⟨q₀L.left, Over.w q₀L⟩ DL hcomplementL.le (hE.mono hdom)
    have hmaps : (⟨qDL.left, Over.w qDL⟩ :
        SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) G_L.X.hom) =
        ⟨(rL ≫ q₀L).left, Over.w (rL ≫ q₀L)⟩ := by
      apply Subtype.ext
      exact congrArg (fun a => a.left) hqL
    exact hmaps.symm ▸ hmod
  have hgeo : geometricRegularMapHasModulus c D G qD :=
    geometricRegularMapHasModulus_of_algebraicClosure c D G qD hDL
  let hDU := hcomplement.trans hD₀U
  refine ⟨d, D, hDU, ?_⟩
  have hmaps : qD = (Over.homMk (V := Over.mk (U.ι ≫ c)) (C.homOfLE hDU.le)
      (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])) ≫ q := by
    refine (Category.assoc r r₀ q).symm.trans ?_
    apply congrArg (fun a => a ≫ q)
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    change (C.homOfLE hcomplement.le ≫ C.homOfLE hD₀U.le) ≫ U.ι = C.homOfLE hDU.le ≫ U.ι
    rw [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  exact hmaps ▸ hgeo

end AlgebraicGeometry.GeneralizedJacobian
