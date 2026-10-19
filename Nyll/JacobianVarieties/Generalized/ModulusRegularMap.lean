/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicallyClosedPointHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ReducedSmoothOverField
import Nyll.JacobianVarieties.Generalized.ModulusAtlasGluing
import Nyll.JacobianVarieties.Generalized.ModulusFamilyPointEvaluation
import Nyll.JacobianVarieties.Generalized.ModulusPointEvaluation
import Nyll.JacobianVarieties.Generalized.GeometricIntegrality
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Generalized.DivisorClassPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelMap
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums

/-! # The constructed regular map for an actual commutative group target

The map uses the group's original operations and the regular morphism's actual
place values. The only modulus input is the principal-divisor condition.
The group-homomorphism and Abel-factorization statements are separate theorems.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)

/-- The genuine regular map on the constructed generalized Jacobian, using only
an actual target group, a regular curve map, and its full modulus condition. -/
def regularMapFromModulus (hmod : M.regularMapHasModulus D G q) (hd : 0 < d) :
    (groupScheme M.toBase D).X ⟶ G.X := by
  let f := M.modulusRegularMap D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q
    (commGroupPointValue G (𝟙 _)) (commGroupPointValue_injective G (𝟙 _))
    (commGroupPointValue_one G (𝟙 _)) (commGroupPointValue_mul G (𝟙 _))
    (M.regularMapValues (modulusComplement (modulusCurveMap D)) G q)
    (M.regularMapValues_apply (modulusComplement (modulusCurveMap D)) G q) hmod hd
  exact Over.homMk f.1 f.2

/-- The constructed regular map induces the original additive divisor evaluation
on every rational point of the actual generalized Jacobian. -/
theorem regularMapFromModulus_point
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d)
    (p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X) :
    Additive.ofMul (p ≫ M.regularMapFromModulus D ε G q hmod hd) =
      M.modulusPointEvaluation D
        (M.regularMapValues (modulusComplement (modulusCurveMap D)) G q) hmod
        (Additive.ofMul p) := by
  have hDimension : SmoothOfRelativeDimension
      (SmoothProperCurve.geometricGenus K M.toBase + (d - 1))
      (groupScheme M.toBase D).X.hom := (geometry M.toBase D).1
  have : LocallyOfFiniteType (groupScheme M.toBase D).X.hom := (geometry M.toBase D).2.1
  have : Smooth (groupScheme M.toBase D).X.hom :=
    SmoothOfRelativeDimension.smooth
      (SmoothProperCurve.geometricGenus K M.toBase + (d - 1)) _
  have : IsReduced (groupScheme M.toBase D).X.left :=
    isReduced_of_smooth_over_field (g := (groupScheme M.toBase D).X.hom) inferInstance
  let atlas := generalizedJacobianDivisorAtlas M.toBase D ε hd
  let v := commGroupPointValue G (𝟙 (Spec (CommRingCat.of K)))
  let a := M.regularMapValues (modulusComplement (modulusCurveMap D)) G q
  obtain ⟨j, z, hz, he⟩ := M.modulusAtlasSum_fieldPoint D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q
    v (commGroupPointValue_injective G (𝟙 _))
    (commGroupPointValue_one G (𝟙 _)) (commGroupPointValue_mul G (𝟙 _))
    a (M.regularMapValues_apply (modulusComplement (modulusCurveMap D)) G q)
    hmod atlas p
  have hs := M.modulusFamilySum_pullback_eq_modulusPointEvaluation D ε G q hmod hd j z
  rw [hz] at hs
  exact (congrArg v he).trans hs

/-- Multiplication of actual rational points is respected by the constructed map. -/
theorem regularMapFromModulus_mul
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d)
    (x y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X) :
    (x * y) ≫ M.regularMapFromModulus D ε G q hmod hd =
      (x ≫ M.regularMapFromModulus D ε G q hmod hd) *
        (y ≫ M.regularMapFromModulus D ε G q hmod hd) := by
  apply Additive.ofMul.injective
  change Additive.ofMul ((x * y) ≫ M.regularMapFromModulus D ε G q hmod hd) =
    Additive.ofMul (x ≫ M.regularMapFromModulus D ε G q hmod hd) +
      Additive.ofMul (y ≫ M.regularMapFromModulus D ε G q hmod hd)
  rw [M.regularMapFromModulus_point D ε G q hmod hd (x * y),
    M.regularMapFromModulus_point D ε G q hmod hd x,
    M.regularMapFromModulus_point D ε G q hmod hd y]
  exact map_add (M.modulusPointEvaluation D
    (M.regularMapValues (modulusComplement (modulusCurveMap D)) G q) hmod)
      (Additive.ofMul x) (Additive.ofMul y)

/-- The regular map obtained from the full modulus condition is an actual
homomorphism of commutative group schemes. -/
def groupHomFromModulus (hmod : M.regularMapHasModulus D G q) (hd : 0 < d) :
    groupScheme M.toBase D ⟶ G := by
  let J := groupScheme M.toBase D
  have hDimension : SmoothOfRelativeDimension
      (SmoothProperCurve.geometricGenus K M.toBase + (d - 1)) J.X.hom :=
    (geometry M.toBase D).1
  have : Smooth J.X.hom :=
    SmoothOfRelativeDimension.smooth
      (SmoothProperCurve.geometricGenus K M.toBase + (d - 1)) _
  have : Smooth (J.X ⊗ J.X).hom := by
    change Smooth (pullback.fst J.X.hom J.X.hom ≫ J.X.hom)
    infer_instance
  have : LocallyOfFiniteType (J.X ⊗ J.X).hom := inferInstance
  have : IsReduced (J.X ⊗ J.X).left :=
    isReduced_of_smooth_over_field (g := (J.X ⊗ J.X).hom) inferInstance
  exact GroupSchemes.homOfAlgebraicallyClosedPoints J G
    (M.regularMapFromModulus D ε G q hmod hd)
    (M.regularMapFromModulus_mul D ε G q hmod hd)

/-- Without a pointedness hypothesis, the genuine Abel factorization is the
original regular map translated by the inverse of its actual basepoint value. -/
theorem groupHomFromModulus_abel_translation
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d) :
    modulusAbelMap M.toBase D (Over.homMk ε.1 ε.2) ≫
        (M.groupHomFromModulus D ε G q hmod hd).hom.hom.hom =
      (Over.homMk q.1 q.2) /
        ((Over.homMk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)
          (Category.comp_id _) :
          Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
            Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫
          (Over.homMk ε.1 ε.2 : Over.mk (𝟙 (Spec (.of K))) ⟶
              Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) ≫
            (Over.homMk q.1 q.2 : Over.mk
              ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ G.X)) := by
  let U := modulusComplement (modulusCurveMap D)
  let qOver : Over.mk (U.ι ≫ M.toBase) ⟶ G.X := Over.homMk q.1 q.2
  let εOver : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk (U.ι ≫ M.toBase) := Over.homMk ε.1 ε.2
  let base : Over.mk (U.ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk (U.ι ≫ M.toBase) (Category.comp_id _)
  have : Smooth (U.ι ≫ M.toBase) := inferInstance
  have : IsReduced (Over.mk (U.ι ≫ M.toBase)).left :=
    isReduced_of_smooth_over_field (g := U.ι ≫ M.toBase) inferInstance
  have : LocallyOfFiniteType (Over.mk (U.ι ≫ M.toBase)).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ M.toBase))
  apply GroupSchemes.hom_ext_algebraicallyClosedPoints
  intro x
  have hxbase : x ≫ base = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Over.w x
  have hconstant : x ≫ (base ≫ εOver ≫ qOver) = εOver ≫ qOver := by
    rw [← Category.assoc, hxbase, Category.id_comp]
  change x ≫ (modulusAbelMap M.toBase D εOver ≫
      (M.groupHomFromModulus D ε G q hmod hd).hom.hom.hom) =
    x ≫ (qOver / (base ≫ εOver ≫ qOver))
  rw [GrpObj.comp_div, hconstant, ← Category.assoc]
  apply Additive.ofMul.injective
  change Additive.ofMul ((x ≫ modulusAbelMap M.toBase D εOver) ≫
      M.regularMapFromModulus D ε G q hmod hd) =
    Additive.ofMul (x ≫ qOver) - Additive.ofMul (εOver ≫ qOver)
  refine (M.regularMapFromModulus_point D ε G q hmod hd _).trans
    ((M.modulusPointEvaluation_abel D εOver x
      (M.regularMapValues U G q) hmod).trans ?_)
  exact congrArg₂ (fun a b => a - b)
    (M.regularMapValues_apply U G q ⟨x.left, Over.w x⟩)
    (M.regularMapValues_apply U G q ε)

/-- The unpointed regular map has a unique group-homomorphism factor after
translation by its actual basepoint value. -/
theorem existsUnique_groupHomFromModulus_translation
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d) :
    ∃! f : groupScheme M.toBase D ⟶ G,
      modulusAbelMap M.toBase D (Over.homMk ε.1 ε.2) ≫ f.hom.hom.hom =
        (Over.homMk q.1 q.2) /
          ((Over.homMk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)
            (Category.comp_id _) :
            Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
              Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫
            (Over.homMk ε.1 ε.2 : Over.mk (𝟙 (Spec (.of K))) ⟶
              Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) ≫
            (Over.homMk q.1 q.2 : Over.mk
              ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ G.X)) := by
  have hf := M.groupHomFromModulus_abel_translation D ε G q hmod hd
  refine ⟨M.groupHomFromModulus D ε G q hmod hd, hf, ?_⟩
  intro f hfac
  exact M.modulusAbel_groupHom_ext D (Over.homMk ε.1 ε.2) G
    f (M.groupHomFromModulus D ε G q hmod hd) (hfac.trans hf.symm)

/-- For a map sending the basepoint to the identity, the constructed group
morphism factors the original regular map through the genuine Abel morphism. -/
theorem groupHomFromModulus_abel
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d)
    (hε : NeronModelInfra.schemeHomOverComp ε q = (commGroupRelativeLaw G).one (𝟙 _)) :
    modulusAbelMap M.toBase D (Over.homMk ε.1 ε.2) ≫
        (M.groupHomFromModulus D ε G q hmod hd).hom.hom.hom =
      Over.homMk q.1 q.2 := by
  let U := modulusComplement (modulusCurveMap D)
  let a := M.regularMapValues U G q
  have : Smooth (U.ι ≫ M.toBase) := inferInstance
  have : IsReduced (Over.mk (U.ι ≫ M.toBase)).left :=
    isReduced_of_smooth_over_field (g := U.ι ≫ M.toBase) inferInstance
  have : LocallyOfFiniteType (Over.mk (U.ι ≫ M.toBase)).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ M.toBase))
  apply GroupSchemes.hom_ext_algebraicallyClosedPoints
  intro x
  apply Additive.ofMul.injective
  change Additive.ofMul
    ((x ≫ modulusAbelMap M.toBase D (Over.homMk ε.1 ε.2)) ≫
      M.regularMapFromModulus D ε G q hmod hd) =
        Additive.ofMul (x ≫ Over.homMk q.1 q.2)
  refine (M.regularMapFromModulus_point D ε G q hmod hd _).trans
    ((M.modulusPointEvaluation_abel D (Over.homMk ε.1 ε.2) x a hmod).trans ?_)
  have hx : a (M.modulusPlace D x) = Additive.ofMul (x ≫ Over.homMk q.1 q.2) :=
    M.regularMapValues_apply U G q ⟨x.left, Over.w x⟩
  have he : a (M.modulusPlace D (Over.homMk ε.1 ε.2)) = 0 := by
    have h := M.regularMapValues_apply U G q ε
    rw [hε, commGroupPointValue_one] at h
    exact h
  change a (M.modulusPlace D x) - a (M.modulusPlace D (Over.homMk ε.1 ε.2)) = _
  rw [hx, he, sub_zero]

/-- Existence and uniqueness for a pointed regular map with its actual positive
modulus over an algebraically closed field. -/
theorem existsUnique_groupHomFromModulus
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d)
    (hε : NeronModelInfra.schemeHomOverComp ε q = (commGroupRelativeLaw G).one (𝟙 _)) :
    ∃! f : groupScheme M.toBase D ⟶ G,
      modulusAbelMap M.toBase D (Over.homMk ε.1 ε.2) ≫ f.hom.hom.hom =
        Over.homMk q.1 q.2 := by
  have hf := M.groupHomFromModulus_abel D ε G q hmod hd hε
  refine ⟨M.groupHomFromModulus D ε G q hmod hd, hf, ?_⟩
  intro f hfac
  exact M.modulusAbel_groupHom_ext D (Over.homMk ε.1 ε.2) G
    f (M.groupHomFromModulus D ε G q hmod hd) (hfac.trans hf.symm)


/-- The constructed group morphism is independent of the auxiliary Abel basepoint,
because both constructions induce the same full-modulus divisor evaluation. -/
theorem groupHomFromModulus_changeBasepoint
    (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
    (hmod : M.regularMapHasModulus D G q) (hd : 0 < d) :
    M.groupHomFromModulus D ε G q hmod hd =
      M.groupHomFromModulus D ε' G q hmod hd := by
  have : LocallyOfFiniteType (groupScheme M.toBase D).X.hom :=
    (geometry M.toBase D).2.1
  apply CommGrp.hom_ext
  apply GroupSchemes.hom_ext_algebraicallyClosedPoints
  intro x
  apply Additive.ofMul.injective
  change Additive.ofMul (x ≫ M.regularMapFromModulus D ε G q hmod hd) =
    Additive.ofMul (x ≫ M.regularMapFromModulus D ε' G q hmod hd)
  exact (M.regularMapFromModulus_point D ε G q hmod hd x).trans
    (M.regularMapFromModulus_point D ε' G q hmod hd x).symm


/-- The constructed universal group factor commutes with an actual homomorphism
of target group schemes; the composite modulus is supplied by functoriality. -/
theorem groupHomFromModulus_comp
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
    (φ : G ⟶ H) (hmod : M.regularMapHasModulus D G q) (hd : 0 < d) :
    let qH : SchemeHomOver
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) H.X.hom :=
      (commGroupPointEquiv H
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          ((commGroupPointEquiv G
            ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) q) ≫
              φ.hom.hom.hom)
    M.groupHomFromModulus D ε H qH (M.regularMapHasModulus_comp D G q hmod H φ) hd =
      M.groupHomFromModulus D ε G q hmod hd ≫ φ := by
  intro qH
  let U := modulusComplement (modulusCurveMap D)
  let a := modulusAbelMap M.toBase D (Over.homMk ε.1 ε.2)
  let qOver : Over.mk (U.ι ≫ M.toBase) ⟶ G.X := Over.homMk q.1 q.2
  let εOver : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk (U.ι ≫ M.toBase) := Over.homMk ε.1 ε.2
  let base : Over.mk (U.ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk (U.ι ≫ M.toBase) (Category.comp_id _)
  apply M.modulusAbel_groupHom_ext D (Over.homMk ε.1 ε.2) H
  change a ≫ (M.groupHomFromModulus D ε H qH
      (M.regularMapHasModulus_comp D G q hmod H φ) hd).hom.hom.hom =
    a ≫ ((M.groupHomFromModulus D ε G q hmod hd).hom.hom.hom ≫ φ.hom.hom.hom)
  calc
    _ = (qOver ≫ φ.hom.hom.hom) /
        (base ≫ εOver ≫ qOver ≫ φ.hom.hom.hom) :=
      M.groupHomFromModulus_abel_translation D ε H qH
        (M.regularMapHasModulus_comp D G q hmod H φ) hd
    _ = (qOver / (base ≫ εOver ≫ qOver)) ≫ φ.hom.hom.hom := by
      rw [GrpObj.div_comp]
      simp only [Category.assoc]
    _ = a ≫ ((M.groupHomFromModulus D ε G q hmod hd).hom.hom.hom ≫
        φ.hom.hom.hom) := by
      exact (congrArg (fun f => f ≫ φ.hom.hom.hom)
        (M.groupHomFromModulus_abel_translation D ε G q hmod hd).symm).trans
          (Category.assoc _ _ _)

end AlgebraicCurve.CurveModel
