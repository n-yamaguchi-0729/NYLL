/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusMapRestriction
import Nyll.JacobianVarieties.Generalized.ModulusClassUniversality
import Nyll.JacobianVarieties.Generalized.LocalUnitTransition

/-! # Full-modulus divisor transitions on actual Jacobian points

The canonical comparison intertwines the divisor-class transition with the
actual scheme group transition. The proof uses the proved generation by Abel
points and the actual Abel square, so it retains the original representatives
and the full multiplicities of both moduli.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.Modulus

private theorem transition_classAbel_away
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {D E : Modulus K F} (h : E ≤ D)
    (w₀ : Place K F) (h₀ : D w₀ = 0) (hdeg : w₀.deg = 1)
    (w : Place K F) (hw : D w = 0) :
    transition h (D.classAbel w₀ h₀ hdeg w) =
      E.classAbel w₀ (Nat.eq_zero_of_le_zero (h₀ ▸ h w₀)) hdeg w := by
  rw [D.classAbel_of_away w₀ h₀ hdeg w hw, transition_mkZero,
    E.classAbel_of_away w₀ _ hdeg w (Nat.eq_zero_of_le_zero (hw ▸ h w))]
  rfl

end AlgebraicCurve.Modulus

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d e : ℕ}
  (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (E : RelEffCartierDiv M.toBase e (𝟙 (Spec (CommRingCat.of K))))
  (hDE : D.I ≤ E.I)

/-- The full divisor-class transition and actual group transition give
the same point under the canonical divisor comparison. -/
theorem divisorClassPointEquiv_transition
    (z : (M.functionFieldModulus D).ClassGroupZero) :
    let h : M.functionFieldModulus E ≤ M.functionFieldModulus D :=
      M.cartierModulus_antitone (modulusCurveIdeal_isInvertible D)
        (modulusCurveIdeal_isInvertible E) (modulusCurveIdeal_mono D E hDE)
    Additive.ofMul ((M.divisorClassPointEquiv D z).toMul ≫
        (GeneralizedJacobian.transition M.toBase D E hDE).hom.hom.hom) =
      M.divisorClassPointEquiv E (Modulus.transition h z) := by
  intro h
  obtain ⟨ε⟩ := modulusComplement_point M.toBase D
  let j := Scheme.IdealSheafData.inclusion hDE
  have w := modulusIdealInclusion_curve M.toBase D E hDE
  let r := modulusComplementRestriction M.toBase j w
  have hplace (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) :
      M.modulusPlace E (x ≫ r) = M.modulusPlace D x := by
    apply congrArg M.pointEquivPlace
    apply Subtype.ext
    change (x.left ≫ M.C.homOfLE (modulusComplement_le_of_restriction j w)) ≫
      (modulusComplement (modulusCurveMap E)).ι =
        x.left ≫ (modulusComplement (modulusCurveMap D)).ι
    rw [Category.assoc, Scheme.homOfLE_ι]
  let φ := (IsMonHom.monoidHom
    (GeneralizedJacobian.transition M.toBase D E hDE).hom.hom.hom
      (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
  have heq := (M.functionFieldModulus D).classAbel_addHom_ext
    (M.modulusPlace D ε) (M.functionFieldModulus_modulusPlace_eq_zero D ε)
    (M.place_deg_eq_one (M.modulusPlace D ε))
    (φ.comp (M.divisorClassPointEquiv D).toAddMonoidHom)
    ((M.divisorClassPointEquiv E).toAddMonoidHom.comp (Modulus.transition h)) (by
      intro v hv
      obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D v hv
      change φ (M.divisorClassPointEquiv D _) =
        M.divisorClassPointEquiv E (Modulus.transition h _)
      rw [M.divisorClassPointEquiv_abel D ε x,
        Modulus.transition_classAbel_away h (M.modulusPlace D ε)
          (M.functionFieldModulus_modulusPlace_eq_zero D ε)
          (M.place_deg_eq_one (M.modulusPlace D ε)) (M.modulusPlace D x) hv]
      have ha := M.divisorClassPointEquiv_abel E (ε ≫ r) (x ≫ r)
      simp only [hplace ε, hplace x] at ha
      rw [ha]
      change Additive.ofMul ((x ≫ modulusAbelMap M.toBase D ε) ≫
          (transitionAlong M.toBase D E j w).hom.hom.hom) =
        Additive.ofMul ((x ≫ r) ≫ modulusAbelMap M.toBase E (ε ≫ r))
      rw [Category.assoc, modulusAbelMap_transitionAlong, Category.assoc])
  exact DFunLike.congr_fun heq z

omit [IsAlgClosed K] [GeometricallyIntegral M.toBase] in
/-- A degree-zero relative divisor has the literal zero function-field
modulus, including all of its stalk multiplicities. -/
theorem functionFieldModulus_zeroDegree
    (D₀ : RelEffCartierDiv M.toBase 0 (𝟙 (Spec (CommRingCat.of K)))) :
    M.functionFieldModulus D₀ = 0 := by
  ext w
  apply (M.cartierModulus_eq_zero_iff (modulusCurveIdeal D₀)
    (modulusCurveIdeal_isInvertible D₀) w).mpr
  rw [modulusCurveIdeal_eq_comap, D₀.I_eq_top_of_degree_zero,
    Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.support_top]
  exact Set.notMem_empty _

/-- Under the actual point comparison, the divisor-class forgetful kernel
is exactly the kernel of the scheme transition to the empty-modulus Jacobian. -/
theorem divisorClassPointEquiv_emptyTransition_kernel
    (D₀ : RelEffCartierDiv M.toBase 0 (𝟙 (Spec (CommRingCat.of K))))
    (z : (M.functionFieldModulus D).ClassGroupZero) :
    let hD₀ : D.I ≤ D₀.I := D₀.I_eq_top_of_degree_zero.symm ▸ le_top
    (M.divisorClassPointEquiv D z).toMul ≫
        (GeneralizedJacobian.transition M.toBase D D₀ hD₀).hom.hom.hom = 1 ↔
      (M.functionFieldModulus D).toPic0 z = 0 := by
  intro hD₀
  let h : M.functionFieldModulus D₀ ≤ M.functionFieldModulus D :=
    M.cartierModulus_antitone (modulusCurveIdeal_isInvertible D)
      (modulusCurveIdeal_isInvertible D₀) (modulusCurveIdeal_mono D D₀ hD₀)
  have he := M.divisorClassPointEquiv_transition D D₀ hD₀ z
  have hi : Function.Injective (M.functionFieldModulus D₀).toPic0 := by
    rw [M.functionFieldModulus_zeroDegree D₀]
    exact Modulus.toPic0_zero_injective
  constructor
  · intro hz
    rw [hz] at he
    have ht : Modulus.transition h z = 0 :=
      (M.divisorClassPointEquiv D₀).injective (he.symm.trans (map_zero _).symm)
    rw [← Modulus.toPic0_transition h z, ht, map_zero]
  · intro hz
    have ht : Modulus.transition h z = 0 := hi (by
      rw [Modulus.toPic0_transition, hz, map_zero])
    apply Additive.ofMul.injective
    exact he.trans ((congrArg (M.divisorClassPointEquiv D₀) ht).trans (map_zero _))

end AlgebraicCurve.CurveModel
