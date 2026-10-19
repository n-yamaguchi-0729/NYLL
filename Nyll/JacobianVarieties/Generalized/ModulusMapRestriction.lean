/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.AlgebraicCurves.Models.Divisors.CartierIdealEquiv
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolConductor
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolUniqueness
import Nyll.JacobianVarieties.Generalized.DivisorClassPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelRestriction
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.JacobianVarieties.Generalized.ModulusCurveIdeal
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusTransition
import Nyll.JacobianVarieties.Generalized.ModulusAbelTransition
import Nyll.JacobianVarieties.Generalized.ModulusRegularMap

/-! # Restricting a regular map while enlarging its full modulus

The ideal inclusion gives both the actual open-curve restriction and the
inequality of all multiplicities. Values at the newly removed points do not
affect the modulus condition because every admissible principal divisor has
order zero there.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  {d e : ℕ}
  (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (E : RelEffCartierDiv M.toBase e (𝟙 (Spec (CommRingCat.of K))))
  (hED : E.I ≤ D.I)
  (G : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)

/-- Enlarging the actual Cartier modulus preserves the modulus condition for
the restricted regular map, with all multiplicities retained. -/
theorem regularMapHasModulus_restrict (hmod : M.regularMapHasModulus D G q) :
    let j : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) ⟶
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) :=
      modulusComplementRestriction M.toBase
      (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve M.toBase E D hED)
    M.regularMapHasModulus E G
      ((commGroupPointEquiv G
        ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase)).symm
          (j ≫ (commGroupPointEquiv G
            ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) q))) := by
  intro j
  have hDE : M.functionFieldModulus D ≤ M.functionFieldModulus E :=
    M.cartierModulus_antitone (modulusCurveIdeal_isInvertible E)
      (modulusCurveIdeal_isInvertible D) (modulusCurveIdeal_mono E D hED)
  have hlarger := Modulus.HasModulus.mono hmod hDE
  apply Modulus.HasModulus.congr hlarger
  intro w hw
  obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq E w hw
  let y := x ≫ j
  have hy : M.openPointPlace (modulusComplement (modulusCurveMap D))
      ⟨y.left, Over.w y⟩ = M.modulusPlace E x := by
    apply congrArg M.pointEquivPlace
    apply Subtype.ext
    change (x.left ≫ M.C.homOfLE
      (modulusComplement_le_of_restriction (Scheme.IdealSheafData.inclusion hED)
        (modulusIdealInclusion_curve M.toBase E D hED))) ≫
        (modulusComplement (modulusCurveMap D)).ι =
      x.left ≫ (modulusComplement (modulusCurveMap E)).ι
    rw [Category.assoc, Scheme.homOfLE_ι]
  have hvalue := M.regularMapValues_apply (modulusComplement (modulusCurveMap D))
    G q ⟨y.left, Over.w y⟩
  rw [hy] at hvalue
  rw [hvalue]
  change commGroupPointValue G (𝟙 _)
      (NeronModelInfra.schemeHomOverComp ⟨y.left, Over.w y⟩ q) =
    M.regularMapValues (modulusComplement (modulusCurveMap E)) G _
      (M.openPointPlace (modulusComplement (modulusCurveMap E)) ⟨x.left, Over.w x⟩)
  rw [M.regularMapValues_apply]
  change Additive.ofMul ((x ≫ j) ≫ (commGroupPointEquiv G _ q)) =
    Additive.ofMul (x ≫ (j ≫ (commGroupPointEquiv G _ q)))
  exact congrArg Additive.ofMul (Category.assoc _ _ _)

/-- The constructed group factors commute with the actual full-modulus
transition. The restricted modulus hypothesis is supplied by ideal containment. -/
theorem groupHomFromModulus_restrict [GeometricallyIntegral M.toBase]
    [IsSeparated G.X.hom]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase))
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d) (he : 0 < e) :
    let r : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) ⟶
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) :=
      modulusComplementRestriction M.toBase
      (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve M.toBase E D hED)
    let qE : SchemeHomOver
        ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) G.X.hom :=
      (commGroupPointEquiv G
      ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase)).symm
        (r ≫ (commGroupPointEquiv G
          ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) q))
    let εD : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) :=
      let p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
          Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) :=
        Over.homMk ε.1 ε.2
      ⟨(p ≫ r).left, Over.w (p ≫ r)⟩
    M.groupHomFromModulus E ε G qE
        (M.regularMapHasModulus_restrict D E hED G q hmod) he =
      transition M.toBase E D hED ≫ M.groupHomFromModulus D εD G q hmod hd := by
  intro r qE εD
  apply M.modulusAbel_groupHom_ext E (Over.homMk ε.1 ε.2) G
  have hE := M.groupHomFromModulus_abel_translation E ε G qE
    (M.regularMapHasModulus_restrict D E hED G q hmod) he
  have hD := M.groupHomFromModulus_abel_translation D εD G q hmod hd
  have hAbel := modulusAbelMap_transitionAlong M.toBase E D
    (Scheme.IdealSheafData.inclusion hED)
    (modulusIdealInclusion_curve M.toBase E D hED) (Over.homMk ε.1 ε.2)
  let bE : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  let bD : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  have hb : r ≫ bD = bE := by
    apply Over.OverMorphism.ext
    exact Over.w r
  change modulusAbelMap M.toBase E (Over.homMk ε.1 ε.2) ≫
      (M.groupHomFromModulus E ε G qE
        (M.regularMapHasModulus_restrict D E hED G q hmod) he).hom.hom.hom =
    modulusAbelMap M.toBase E (Over.homMk ε.1 ε.2) ≫
      ((transition M.toBase E D hED).hom.hom.hom ≫
        (M.groupHomFromModulus D εD G q hmod hd).hom.hom.hom)
  change modulusAbelMap M.toBase E (Over.homMk ε.1 ε.2) ≫
      (transition M.toBase E D hED).hom.hom.hom =
    r ≫ modulusAbelMap M.toBase D (Over.homMk εD.1 εD.2) at hAbel
  rw [← Category.assoc, hAbel, Category.assoc, hD, hE, GrpObj.comp_div]
  let p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) :=
    Over.homMk ε.1 ε.2
  change (r ≫ Over.homMk q.1 q.2) /
      (bE ≫ p ≫ r ≫ Over.homMk q.1 q.2) =
    (r ≫ Over.homMk q.1 q.2) /
      (r ≫ bD ≫ (p ≫ r) ≫ Over.homMk q.1 q.2)
  rw [← Category.assoc r bD, hb, Category.assoc]

omit [IsAlgClosed K] in
/-- The complement of any larger finite modulus is dense in the original
curve. Agreement there determines a regular map to a separated target. -/
theorem modulusComplementRestriction_hom_ext [GeometricallyIntegral M.toBase]
    {Y : Over (Spec (CommRingCat.of K))} [IsSeparated Y.hom]
    (f g : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ Y)
    (h : modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
          (modulusIdealInclusion_curve M.toBase E D hED) ≫ f =
        modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
          (modulusIdealInclusion_curve M.toBase E D hED) ≫ g) : f = g := by
  let U := modulusComplement (modulusCurveMap E)
  let r := modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
    (modulusIdealInclusion_curve M.toBase E D hED)
  have hU : (U : Set M.C).Nonempty := by
    obtain ⟨x⟩ := modulusComplement_nonempty M.toBase E
    exact ⟨x.1, x.2⟩
  have hdense : Dense (U : Set M.C) := U.isOpen.dense hU
  have : IsDominant r.left :=
    Opens.isDominant_homOfLE hdense
      (modulusComplement_le_of_restriction (Scheme.IdealSheafData.inclusion hED)
        (modulusIdealInclusion_curve M.toBase E D hED))
  let : IsReduced (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫
      M.toBase)).left :=
    (inferInstance : IsReduced ((modulusComplement (modulusCurveMap D)) : Scheme))
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated Y.hom
    ((Over.w f).trans (Over.w g).symm) r.left
    (congrArg (fun t => t.left) h)

end AlgebraicCurve.CurveModel
