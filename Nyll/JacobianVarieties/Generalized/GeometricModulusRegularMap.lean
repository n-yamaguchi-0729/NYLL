/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusAtlasGluing
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusPointEvaluation
import Nyll.JacobianVarieties.Generalized.ModulusAbelMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelChangeBasepoint
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ReducedSmoothOverField
import Nyll.JacobianVarieties.Generalized.GeometricModulusRegularMapPoint
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric
import Nyll.SchemeTheory.GroupSchemes.GeometricPointHom
import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # The actual group morphism constructed over an arbitrary field

The regular map was glued on the original divisor atlas. Its geometric
point formula identifies multiplication with addition under the original
full-modulus evaluation. The geometric-point criterion then proves the
group law for this same regular map.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ c) G.X.hom)
  (hmod : geometricRegularMapHasModulus c D G (Over.homMk q.1 q.2))

private abbrev geometricModulusBasepoint :
    Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) := Over.homMk ε.1 ε.2

private abbrev geometricModulusTargetMap :
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X := Over.homMk q.1 q.2

omit [IsSeparated G.X.hom] in
private theorem commGroupPointValue_comp_apply {T U : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (s : U ⟶ Spec (CommRingCat.of K))
    (x : Over.mk t ⟶ Over.mk s) (y : Over.mk s ⟶ G.X) :
    commGroupPointValue G t
      (NeronModelInfra.schemeHomOverComp ⟨x.left, Over.w x⟩ ⟨y.left, Over.w y⟩) =
        Additive.ofMul (x ≫ y) := rfl

local notation "ε₀" => geometricModulusBasepoint c D ε
local notation "q₀" => geometricModulusTargetMap c D G q

/-- The regular map respects products on every closed extension field. -/
theorem geometricModulusRegularMap_mul (hd : 0 < d)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x y : (Over.map (specMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
      (groupScheme c D).X) :
    let f := geometricModulusRegularMap c D ε G q hmod hd
    (x * y) ≫ Over.homMk f.1 f.2 =
      (x ≫ Over.homMk f.1 f.2) * (y ≫ Over.homMk f.1 f.2) := by
  intro f
  let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let φ := (Over.mapPullbackAdj (specMap K L)).homMulEquiv T G.X
  apply φ.injective
  rw [map_mul]
  apply Additive.ofMul.injective
  change Additive.ofMul ((Over.mapPullbackAdj (specMap K L)).homEquiv T G.X
      ((x * y) ≫ Over.homMk f.1 f.2)) =
    Additive.ofMul ((Over.mapPullbackAdj (specMap K L)).homEquiv T G.X
      (x ≫ Over.homMk f.1 f.2)) +
    Additive.ofMul ((Over.mapPullbackAdj (specMap K L)).homEquiv T G.X
      (y ≫ Over.homMk f.1 f.2))
  rw [geometricModulusRegularMap_point c D ε G q hmod hd L (x * y),
    geometricModulusRegularMap_point c D ε G q hmod hd L x,
    geometricModulusRegularMap_point c D ε G q hmod hd L y,
    map_mul (groupScalarExtensionPointEquiv c D L T).symm]
  exact map_add _ _ _

/-- The regular map over the original field, with its proved group law. -/
def geometricGroupHomFromModulus (hd : 0 < d) : groupScheme c D ⟶ G := by
  let J := groupScheme c D
  have : SmoothOfRelativeDimension (geometricGenus K c + (d - 1)) J.X.hom :=
    (geometry c D).1
  have : Smooth J.X.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + (d - 1)) _
  have : Smooth (J.X ⊗ J.X).hom := by
    change Smooth (pullback.fst J.X.hom J.X.hom ≫ J.X.hom)
    infer_instance
  have : IsReduced (J.X ⊗ J.X).left :=
    isReduced_of_smooth_over_field (g := (J.X ⊗ J.X).hom) inferInstance
  let f := geometricModulusRegularMap c D ε G q hmod hd
  let fOver : J.X ⟶ G.X := Over.homMk f.1 f.2
  have : IsMonHom fOver := by
    apply GroupSchemes.isMonHom_of_algebraicGeometricPoints J G fOver
    intro L fieldL algebraL closedL x y
    let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
    let e : Over.mk (specMap K L) ≅ (Over.map (specMap K L)).obj T :=
      Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ (𝟙 _ ≫ specMap K L) = specMap K L
        rw [Category.id_comp, Category.id_comp])
    apply (cancel_epi e.inv).mp
    rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul,
      ← Category.assoc, ← Category.assoc]
    exact geometricModulusRegularMap_mul c D ε G q hmod hd L
      (e.inv ≫ x) (e.inv ≫ y)
  exact InducedCategory.homMk (Grp.homMk fOver)


/-- On every geometric point of the curve, the constructed map gives its
original value minus the value at the chosen basepoint. -/
theorem geometricGroupHomFromModulus_abel_extensionPoint (hd : 0 < d)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : (Over.map (specMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    let b : (Over.map (specMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk (𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L) (Category.comp_id _)
    (x ≫ modulusAbelMap c D ε₀) ≫
        (geometricGroupHomFromModulus c D ε G q hmod hd).hom.hom.hom =
      (x ≫ q₀) / (b ≫ ε₀ ≫ q₀) := by
  intro b
  let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let cL := baseChange K c L
  let DL := D.changeBaseOfIdentity (specMap K L)
  let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
  let εL := modulusBasepointScalarExtension c D L ε₀
  let qL := modulusGroupMapScalarExtension c D L G q₀
  let xL := divisorScalarExtensionPointLift c D L x
  let : Algebra L (pullback c (specMap K L)).functionField :=
    (AlgebraicCurve.baseToFunctionField cL).toAlgebra
  let ML := AlgebraicCurve.CurveModel.ofSmoothProperCurve cL
  have : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  have hmodL : ML.regularMapHasModulus DL G_L ⟨qL.left, Over.w qL⟩ := hmod L
  let φ : ((Over.map (specMap K L)).obj T ⟶ G.X) ≃* (T ⟶ G_L.X) :=
    (Over.mapPullbackAdj (specMap K L)).homMulEquiv T G.X
  let e := groupScalarExtensionPointEquiv c D L T
  have hAbel : e.symm (x ≫ modulusAbelMap c D ε₀) =
      xL ≫ modulusAbelMap cL DL εL := by
    apply e.symm_apply_eq.mpr
    exact ((groupScalarExtensionPointEquiv_modulusAbelMap c D L
      ε₀ xL).trans
        (congrArg (fun y => y ≫ modulusAbelMap c D ε₀)
          (divisorScalarExtensionPoint_lift c D L x))).symm
  have hx := geometricModulusRegularMap_point c D ε G q hmod hd L
    (x ≫ modulusAbelMap c D ε₀)
  change Additive.ofMul (φ ((x ≫ modulusAbelMap c D ε₀) ≫
      (geometricGroupHomFromModulus c D ε G q hmod hd).hom.hom.hom)) =
    ML.modulusPointEvaluation DL
      (ML.regularMapValues (modulusComplement (modulusCurveMap DL)) G_L
        ⟨qL.left, Over.w qL⟩) hmodL
      (Additive.ofMul (e.symm (x ≫ modulusAbelMap c D ε₀))) at hx
  rw [hAbel] at hx
  have hx := hx.trans (ML.modulusPointEvaluation_abel DL εL xL
    (ML.regularMapValues (modulusComplement (modulusCurveMap DL)) G_L
      ⟨qL.left, Over.w qL⟩) hmodL)
  have hvx := ML.regularMapValues_apply (modulusComplement (modulusCurveMap DL))
    G_L ⟨qL.left, Over.w qL⟩ ⟨xL.left, Over.w xL⟩
  have hvε := ML.regularMapValues_apply (modulusComplement (modulusCurveMap DL))
    G_L ⟨qL.left, Over.w qL⟩ ⟨εL.left, Over.w εL⟩
  rw [show ML.openPointPlace (modulusComplement (modulusCurveMap DL))
    ⟨xL.left, Over.w xL⟩ = ML.modulusPlace DL xL from rfl] at hvx
  rw [show ML.openPointPlace (modulusComplement (modulusCurveMap DL))
    ⟨εL.left, Over.w εL⟩ = ML.modulusPlace DL εL from rfl] at hvε
  have hvx := hvx.trans (commGroupPointValue_comp_apply G_L (𝟙 _)
    ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase) xL qL)
  have hvε := hvε.trans (commGroupPointValue_comp_apply G_L (𝟙 _)
    ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase) εL qL)
  have hqx : xL ≫ qL = φ (x ≫ q₀) := by
    exact (modulusGroupMapScalarExtension_point c D L G q₀ xL).trans
      (congrArg (fun y => φ (y ≫ q₀))
        (divisorScalarExtensionPoint_lift c D L x))
  have hqε : εL ≫ qL = φ (b ≫ ε₀ ≫ q₀) := by
    have hproject : divisorScalarExtensionPoint c D L εL = b ≫ ε₀ :=
      divisorScalarExtensionPoint_lift c D L _
    exact (modulusGroupMapScalarExtension_point c D L G q₀ εL).trans
      ((congrArg (fun y => φ (y ≫ q₀)) hproject).trans
        (congrArg φ (Category.assoc b ε₀ q₀)))
  apply φ.injective
  rw [map_div]
  apply Additive.ofMul.injective
  exact hx.trans (congrArg₂ (fun (a b : Additive (T ⟶ G_L.X)) => a - b)
    (hvx.trans (congrArg Additive.ofMul hqx))
    (hvε.trans (congrArg Additive.ofMul hqε)))


/-- Over the original field, the same group morphism factors the Abel map
with the actual basepoint translation. -/
theorem geometricGroupHomFromModulus_abel_translation (hd : 0 < d) :
    let base : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
    modulusAbelMap c D ε₀ ≫
        (geometricGroupHomFromModulus c D ε G q hmod hd).hom.hom.hom =
      q₀ /
        (base ≫ ε₀ ≫ q₀) := by
  intro base
  let U := modulusComplement (modulusCurveMap D)
  have : Smooth (U.ι ≫ c) := inferInstance
  have : IsReduced (Over.mk (U.ι ≫ c)).left :=
    isReduced_of_smooth_over_field (g := U.ι ≫ c) inferInstance
  apply GroupSchemes.hom_ext_geometricPoints
  intro L fieldL closedL a x
  let : Algebra K L := (Spec.preimage a).hom.toAlgebra
  have ha : specMap K L = a := Spec.map_preimage a
  let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let e : Over.mk a ≅ (Over.map (specMap K L)).obj T :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (𝟙 _ ≫ specMap K L) = a
      rw [Category.id_comp, Category.id_comp, ha])
  let b : (Over.map (specMap K L)).obj T ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk (𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L) (Category.comp_id _)
  have hb : (e.inv ≫ x) ≫ base = b := by
    apply Over.OverMorphism.ext
    exact Over.w (e.inv ≫ x)
  apply (cancel_epi e.inv).mp
  calc
    e.inv ≫ (x ≫ (modulusAbelMap c D ε₀ ≫
        (geometricGroupHomFromModulus c D ε G q hmod hd).hom.hom.hom)) =
      ((e.inv ≫ x) ≫ modulusAbelMap c D ε₀) ≫
        (geometricGroupHomFromModulus c D ε G q hmod hd).hom.hom.hom := by
      simp only [Category.assoc]
    _ = ((e.inv ≫ x) ≫ q₀) /
        (b ≫ ε₀ ≫ q₀) :=
      geometricGroupHomFromModulus_abel_extensionPoint c D ε G q hmod hd L (e.inv ≫ x)
    _ = e.inv ≫ (x ≫ (q₀ /
        (base ≫ ε₀ ≫ q₀))) := by
      rw [GrpObj.comp_div, GrpObj.comp_div]
      simp only [← Category.assoc, hb]

/-- The translated Abel identity in the original over-category point coordinates. -/
theorem geometricGroupHomFromModulus_abel_translation_over
    (εOver : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (qOver : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (hOver : geometricRegularMapHasModulus c D G qOver) (hd : 0 < d) :
    let base : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
    modulusAbelMap c D εOver ≫
        (geometricGroupHomFromModulus c D ⟨εOver.left, Over.w εOver⟩ G
          ⟨qOver.left, Over.w qOver⟩ hOver hd).hom.hom.hom =
      qOver / (base ≫ εOver ≫ qOver) := by
  simpa only [geometricModulusBasepoint, geometricModulusTargetMap, Over.homMk_eta] using
    (geometricGroupHomFromModulus_abel_translation c D ⟨εOver.left, Over.w εOver⟩ G
      ⟨qOver.left, Over.w qOver⟩ hOver hd)

include hmod in
/-- Positive full modulus gives a unique translated Abel factor over every
field with a chosen rational point outside the modulus. -/
theorem existsUnique_geometricGroupHomFromModulus_translation (hd : 0 < d) :
    let base : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
    ∃! f : groupScheme c D ⟶ G,
      modulusAbelMap c D ε₀ ≫ f.hom.hom.hom =
        q₀ /
          (base ≫ ε₀ ≫ q₀) := by
  intro base
  have hf := geometricGroupHomFromModulus_abel_translation c D ε G q hmod hd
  refine ⟨geometricGroupHomFromModulus c D ε G q hmod hd, hf, ?_⟩
  intro f hfac
  exact modulusAbel_groupHom_ext c D ε₀ G
    f (geometricGroupHomFromModulus c D ε G q hmod hd) (hfac.trans hf.symm)


/-- Changing the auxiliary rational point leaves the actual group factor
unchanged over an arbitrary field. -/
theorem geometricGroupHomFromModulus_changeBasepoint (hd : 0 < d)
    (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    geometricGroupHomFromModulus c D ε G q hmod hd =
      geometricGroupHomFromModulus c D ε' G q hmod hd := by
  apply modulusAbel_groupHom_ext c D (Over.homMk ε'.1 ε'.2) G
  have hfac := modulusAbelMap_factor_changeBasepoint c D
    ε₀ (Over.homMk ε'.1 ε'.2) G
    (geometricGroupHomFromModulus c D ε G q hmod hd) q₀
    (geometricGroupHomFromModulus_abel_translation c D ε G q hmod hd)
  exact hfac.trans (geometricGroupHomFromModulus_abel_translation c D ε' G q hmod hd).symm

/-- The actual factor over the ground field commutes with homomorphisms of
separated commutative target groups. -/
theorem geometricGroupHomFromModulus_comp (hd : 0 < d)
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
    (φ : G ⟶ H) :
    let qH : SchemeHomOver
        ((modulusComplement (modulusCurveMap D)).ι ≫ c) H.X.hom :=
      ⟨q.1 ≫ φ.hom.hom.hom.left, by rw [Category.assoc, Over.w, q.2]⟩
    geometricGroupHomFromModulus c D ε H qH
        (geometricRegularMapHasModulus_comp c D G H q₀ hmod φ) hd =
      geometricGroupHomFromModulus c D ε G q hmod hd ≫ φ := by
  intro qH
  let U := modulusComplement (modulusCurveMap D)
  let a := modulusAbelMap c D ε₀
  let qOver : Over.mk (U.ι ≫ c) ⟶ G.X := q₀
  let εOver : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk (U.ι ≫ c) := ε₀
  let base : Over.mk (U.ι ≫ c) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk (U.ι ≫ c) (Category.comp_id _)
  apply modulusAbel_groupHom_ext c D ε₀ H
  change a ≫ (geometricGroupHomFromModulus c D ε H qH
      (geometricRegularMapHasModulus_comp c D G H q₀ hmod φ) hd).hom.hom.hom =
    a ≫ ((geometricGroupHomFromModulus c D ε G q hmod hd).hom.hom.hom ≫ φ.hom.hom.hom)
  calc
    _ = (qOver ≫ φ.hom.hom.hom) / (base ≫ εOver ≫ qOver ≫ φ.hom.hom.hom) :=
      geometricGroupHomFromModulus_abel_translation c D ε H qH
        (geometricRegularMapHasModulus_comp c D G H q₀ hmod φ) hd
    _ = (qOver / (base ≫ εOver ≫ qOver)) ≫ φ.hom.hom.hom := by
      rw [GrpObj.div_comp]
      simp only [Category.assoc]
    _ = a ≫ ((geometricGroupHomFromModulus c D ε G q hmod hd).hom.hom.hom ≫
        φ.hom.hom.hom) := by
      exact (congrArg (fun z => z ≫ φ.hom.hom.hom)
        (geometricGroupHomFromModulus_abel_translation c D ε G q hmod hd).symm).trans
          (Category.assoc _ _ _)

end AlgebraicGeometry.GeneralizedJacobian
