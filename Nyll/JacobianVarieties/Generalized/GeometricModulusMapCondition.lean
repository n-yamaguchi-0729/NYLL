/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapTranslation
import Nyll.JacobianVarieties.Generalized.ModulusAbelMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap
import Nyll.JacobianVarieties.Generalized.PicardOneEquivariantMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelOneScalarExtension

/-! # The full geometric modulus condition over an arbitrary field

The condition is tested on the original principal-divisor relation after
actual extension of the curve, divisor, and target group. It contains no
assumed factorization, descent datum, or comparison morphism.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The full principal-divisor modulus condition after every algebraically
closed extension, evaluated on the actual extended regular map. -/
def geometricRegularMapHasModulus
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L],
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let _ : Algebra L (CategoryTheory.Limits.pullback c (specMap K L)).functionField :=
      (AlgebraicCurve.baseToFunctionField cL).toAlgebra
    let ML := AlgebraicCurve.CurveModel.ofSmoothProperCurve cL
    let qL := modulusGroupMapScalarExtension c D L G q
    ML.regularMapHasModulus DL ((GroupSchemes.baseChange (specMap K L)).obj G)
      ⟨qL.left, Over.w qL⟩

/-- The full modulus of a torsor-valued curve map is tested after actual
algebraically closed extensions, in every choice of target coordinates.
No rational point over the ground field and no factorization are assumed. -/
def geometricTorsorMapHasModulus
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (Q : Over (Spec (CommRingCat.of K))) [ModObj G.X Q]
    [IsIso (ModObj.leftSMul G.X Q)]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L],
    let F := Over.pullback (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
    let _ : ModObj extendedGroup.X (F.obj Q) := F.modObjObj G.X Q
    let _ : IsIso (ModObj.leftSMul extendedGroup.X (F.obj Q)) := F.isIso_leftSMul_modObjObj G.X Q
    let _ : Algebra L (CategoryTheory.Limits.pullback c (specMap K L)).functionField :=
      (AlgebraicCurve.baseToFunctionField cL).toAlgebra
    let ML := AlgebraicCurve.CurveModel.ofSmoothProperCurve cL
    let qL := modulusMapScalarExtension c D L Q q
    ∀ p : MonoidalCategory.tensorUnit (Over (Spec (CommRingCat.of L))) ⟶ F.obj Q,
      ML.regularMapHasModulus DL extendedGroup
        ((commGroupPointEquiv extendedGroup
          ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
            (qL ≫ SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p))

/-- When a target origin exists over the ground field, the intrinsic torsor
condition is exactly the group condition in those coordinates. Translation
invariance over each closed extension proves independence of every other origin. -/
theorem geometricTorsorMapHasModulus_iff_coordinate
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (Q : Over (Spec (CommRingCat.of K))) [ModObj G.X Q]
    [IsIso (ModObj.leftSMul G.X Q)]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (p : MonoidalCategory.tensorUnit (Over (Spec (CommRingCat.of K))) ⟶ Q) :
    geometricTorsorMapHasModulus c D G Q q ↔
      geometricRegularMapHasModulus c D G
        (q ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p) := by
  constructor
  · intro h L fieldL algebraL closedL cL DL algL ML qL
    let F := Over.pullback (specMap K L)
    let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
    let _ : ModObj extendedGroup.X (F.obj Q) := F.modObjObj G.X Q
    have : IsIso (ModObj.leftSMul extendedGroup.X (F.obj Q)) := F.isIso_leftSMul_modObjObj G.X Q
    let pL := Functor.LaxMonoidal.ε F ≫ F.map p
    have hc := h L pL
    have heq : qL = modulusMapScalarExtension c D L Q q ≫
        SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) pL :=
      modulusMapScalarExtension_coordinate c D L G Q p q
    change ML.regularMapHasModulus DL extendedGroup
      ((commGroupPointEquiv extendedGroup
        ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm qL)
    rw [heq]
    exact hc
  · intro h L fieldL algebraL closedL F cL DL extendedGroup action torsor algL ML qL pL
    let p₀ := Functor.LaxMonoidal.ε F ≫ F.map p
    let q₀ := modulusGroupMapScalarExtension c D L G
      (q ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p)
    have hc : ML.regularMapHasModulus DL extendedGroup ⟨q₀.left, Over.w q₀⟩ := h L
    have heq : q₀ = qL ≫ SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p₀ :=
      modulusMapScalarExtension_coordinate c D L G Q p q
    change ML.regularMapHasModulus DL extendedGroup
      ((commGroupPointEquiv extendedGroup
        ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm q₀) at hc
    rw [heq] at hc
    exact ML.regularMapHasModulus_torsorCoordinate_changeBasepoint
      DL extendedGroup (F.obj Q) qL p₀ pL hc


/-- An actual equivariant map of target torsors preserves the full
geometric modulus. Over each closed extension, a point of the extended
curve supplies an origin; translation invariance then handles every
target origin. No rational origin over the ground field is required. -/
theorem geometricTorsorMapHasModulus_comp
    (G H : CommGrp (Over (Spec (CommRingCat.of K))))
    (P Q : Over (Spec (CommRingCat.of K)))
    [ModObj G.X P] [IsIso (ModObj.leftSMul G.X P)]
    [ModObj H.X Q] [IsIso (ModObj.leftSMul H.X Q)]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ P)
    (hmod : geometricTorsorMapHasModulus c D G P q)
    (φ : G ⟶ H) (f : P ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K))) (g : T ⟶ G.X) (x : T ⟶ P),
      (g • x) ≫ f = (g ≫ φ.hom.hom.hom) • (x ≫ f)) :
    geometricTorsorMapHasModulus c D H Q (q ≫ f) := by
  intro L fieldL algebraL closedL F cL DL HL targetAction targetTorsor algL ML rL p
  let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
  let _ : ModObj extendedGroup.X (F.obj P) := F.modObjObj G.X P
  have : IsIso (ModObj.leftSMul extendedGroup.X (F.obj P)) := F.isIso_leftSMul_modObjObj G.X P
  let qL := modulusMapScalarExtension c D L P q
  let φL := (GroupSchemes.baseChange (specMap K L)).map φ
  let fL := F.map f
  obtain ⟨ε⟩ := modulusComplement_point cL DL
  let p₀ := ε ≫ qL
  have hfL : ∀ (T : Over (Spec (CommRingCat.of L)))
      (g : T ⟶ extendedGroup.X) (x : T ⟶ F.obj P),
      (g • x) ≫ fL = (g ≫ φL.hom.hom.hom) • (x ≫ fL) :=
    F.map_modObj_equivariant φ.hom.hom.hom f hf
  have hcoord :
      fL ≫ SchemeTheory.PointedTorsor.coordinate (G := HL.X) (p₀ ≫ fL) =
        SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p₀ ≫ φL.hom.hom.hom := by
    have hmap := SchemeTheory.PointedTorsor.map_unique φL.hom.hom.hom
      p₀ (p₀ ≫ fL) fL rfl hfL
    calc
      _ = SchemeTheory.PointedTorsor.map φL.hom.hom.hom p₀ (p₀ ≫ fL) ≫
          SchemeTheory.PointedTorsor.coordinate (G := HL.X) (p₀ ≫ fL) :=
        congrArg (fun a => a ≫
          SchemeTheory.PointedTorsor.coordinate (G := HL.X) (p₀ ≫ fL)) hmap
      _ = _ := SchemeTheory.PointedTorsor.map_coordinate φL.hom.hom.hom p₀ (p₀ ≫ fL)
  let q₀ : SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) extendedGroup.X.hom :=
    (commGroupPointEquiv extendedGroup ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      (qL ≫ SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p₀)
  have hq₀ : ML.regularMapHasModulus DL extendedGroup q₀ := hmod L p₀
  have hq₁ := ML.regularMapHasModulus_comp DL extendedGroup q₀ hq₀ HL φL
  change ML.regularMapHasModulus DL HL
    ((commGroupPointEquiv HL ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      ((qL ≫ SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p₀) ≫
        φL.hom.hom.hom)) at hq₁
  rw [Category.assoc, ← hcoord, ← Category.assoc] at hq₁
  have hr : rL = qL ≫ fL := modulusMapScalarExtension_comp c D L P Q q f
  rw [hr]
  exact ML.regularMapHasModulus_torsorCoordinate_changeBasepoint DL HL (F.obj Q)
    (qL ≫ fL) (p₀ ≫ fL) p hq₁

/-- Composing with an actual group morphism preserves the full geometric
principal-divisor condition over every base field. -/
theorem geometricRegularMapHasModulus_comp
    (G H : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (hmod : geometricRegularMapHasModulus c D G q) (φ : G ⟶ H) :
    geometricRegularMapHasModulus c D H (q ≫ φ.hom.hom.hom) := by
  intro L fieldL algebraL closedL cL DL algL ML qL
  let r := modulusGroupMapScalarExtension c D L G q
  let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
  let HL := (GroupSchemes.baseChange (specMap K L)).obj H
  let φL := (GroupSchemes.baseChange (specMap K L)).map φ
  have hr : ML.regularMapHasModulus DL extendedGroup ⟨r.left, Over.w r⟩ := hmod L
  have hc := ML.regularMapHasModulus_comp DL extendedGroup ⟨r.left, Over.w r⟩ hr HL φL
  have heq :
      (commGroupPointEquiv HL ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
        (r ≫ φL.hom.hom.hom) =
      (⟨qL.left, Over.w qL⟩ :
        SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) HL.X.hom) := by
    apply Subtype.ext
    exact congrArg Over.Hom.left (modulusGroupMapScalarExtension_comp c D L G H q φ).symm
  change ML.regularMapHasModulus DL HL
    ((commGroupPointEquiv HL ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      (r ≫ φL.hom.hom.hom)) at hc
  rw [heq] at hc
  exact hc

/-- Translating by an actual rational group point preserves the geometric
full modulus over an arbitrary field. -/
theorem geometricRegularMapHasModulus_translate
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (hmod : geometricRegularMapHasModulus c D G q)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    geometricRegularMapHasModulus c D G (q / (b ≫ z)) := by
  intro b L fieldL algebraL closedL cL DL algL ML qL
  let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
  let r := modulusGroupMapScalarExtension c D L G q
  let zL := (Over.mapPullbackAdj (specMap K L)).homEquiv
    (Over.mk (𝟙 (Spec (CommRingCat.of L)))) G.X
      (Over.homMk (𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L)
        (Category.comp_id _) ≫ z)
  let bL : Over.mk ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
    Over.homMk _ (Category.comp_id _)
  have hr : ML.regularMapHasModulus DL extendedGroup ⟨r.left, Over.w r⟩ := hmod L
  have h := ML.regularMapHasModulus_translate DL extendedGroup ⟨r.left, Over.w r⟩ hr zL
  have heq : qL = r / (bL ≫ zL) :=
    modulusGroupMapScalarExtension_translation c D L G q z
  change ML.regularMapHasModulus DL extendedGroup
    ((commGroupPointEquiv extendedGroup ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm qL)
  rw [heq]
  exact h


/-- Translating back by the inverse rational point recovers the original
map, so the full geometric modulus is preserved in both directions. -/
theorem geometricRegularMapHasModulus_translate_iff
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    geometricRegularMapHasModulus c D G q ↔
      geometricRegularMapHasModulus c D G (q / (b ≫ z)) := by
  intro b
  refine ⟨fun h => geometricRegularMapHasModulus_translate c D G q h z, ?_⟩
  intro h
  have hback := geometricRegularMapHasModulus_translate c D G (q / (b ≫ z)) h z⁻¹
  change geometricRegularMapHasModulus c D G ((q / (b ≫ z)) / (b ≫ z⁻¹)) at hback
  rw [GrpObj.comp_inv, div_inv_eq_mul, div_mul_cancel] at hback
  exact hback

/-- The geometric full modulus of a torsor-valued regular map is independent
of the point used as the origin of its coordinates, over every field. -/
theorem geometricRegularMapHasModulus_torsorCoordinate_changeBasepoint
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (P : Over (Spec (CommRingCat.of K))) [ModObj G.X P]
    [IsIso (ModObj.leftSMul G.X P)]
    (r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ P)
    (p p' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P)
    (hmod : geometricRegularMapHasModulus c D G
      (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p)) :
    geometricRegularMapHasModulus c D G
      (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p') := by
  rw [modulusTorsorCoordinate_changeBasepoint c D G P r p p']
  exact geometricRegularMapHasModulus_translate c D G
    (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p) hmod
    (p' ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p)

/-- Over an arbitrary field, the actual pointed Abel map has its full
geometric modulus, with every multiplicity of the given divisor retained. -/
theorem geometricRegularMapHasModulus_abel
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    geometricRegularMapHasModulus c D (groupScheme c D) (modulusAbelMap c D ε) := by
  intro L fieldL algebraL closedL cL DL algL ML qL
  have : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  let εL := modulusBasepointScalarExtension c D L ε
  let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D)
  let e := groupActualScalarExtensionIso c D L
  let a : SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)
      (groupScheme cL DL).X.hom :=
    ⟨(modulusAbelMap cL DL εL).left, Over.w (modulusAbelMap cL DL εL)⟩
  have hmod := ML.regularMapHasModulus_comp DL (groupScheme cL DL) a
    (ML.regularMapHasModulus_abel DL εL) extendedGroup e.inv
  have hfac : modulusAbelMap cL DL εL ≫ e.inv.hom.hom.hom = qL := by
    have h := modulusGroupMapScalarExtension_abel_comp c D L (groupScheme c D) (𝟙 _) ε
    rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    change modulusAbelMap cL DL εL ≫ e.inv.hom.hom.hom =
      modulusGroupMapScalarExtension c D L (groupScheme c D)
        (modulusAbelMap c D ε ≫ 𝟙 _) at h
    simpa only [Category.comp_id] using h
  have heq :
      (commGroupPointEquiv extendedGroup ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
        (modulusAbelMap cL DL εL ≫ e.inv.hom.hom.hom) =
      (⟨qL.left, Over.w qL⟩ :
        SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) extendedGroup.X.hom) := by
    apply Subtype.ext
    exact congrArg Over.Hom.left hfac
  change ML.regularMapHasModulus DL extendedGroup
    ((commGroupPointEquiv extendedGroup ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      (modulusAbelMap cL DL εL ≫ e.inv.hom.hom.hom)) at hmod
  rw [heq] at hmod
  exact hmod


/-- The intrinsic Abel map has the full geometric torsor modulus over
every field and in every degree. An origin is chosen only after a closed
extension, and the native group and torsor comparisons identify its
coordinates with the actual pointed Abel map. -/
theorem geometricTorsorMapHasModulus_abelOne :
    geometricTorsorMapHasModulus c D (groupScheme c D) (picardOne c D) (abelOneMap c D) := by
  intro L fieldL algebraL closedL F cL DL extendedGroup action torsor algL ML qL p
  have : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  let eG := groupActualScalarExtensionIso c D L
  let eP := picardOneScalarExtensionIso c D L
  obtain ⟨ε⟩ := modulusComplement_point cL DL
  let p₀ := ε ≫ qL
  have habel : qL ≫ eP.hom = abelOneMap cL DL := by
    have hp := modulusMapScalarExtension_point c D L (picardOne c D)
      (abelOneMap c D) (𝟙 _)
    rw [Category.id_comp] at hp
    exact (congrArg (fun f => f ≫ eP.hom) hp).trans (by
      simpa only [Category.id_comp] using abelOneMap_scalarExtension c D L (𝟙 _))
  have hp : p₀ ≫ eP.hom = ε ≫ abelOneMap cL DL := by
    change (ε ≫ qL) ≫ eP.hom = ε ≫ abelOneMap cL DL
    rw [Category.assoc, habel]
  have hcoord :
      (qL ≫ SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p₀) ≫ eG.hom.hom.hom.hom =
        abelOneMap cL DL ≫ SchemeTheory.PointedTorsor.coordinate
          (G := (groupScheme cL DL).X) (ε ≫ abelOneMap cL DL) := by
    apply SchemeTheory.PointedTorsor.coordinate_unique
    rw [← hp, ← Category.assoc,
      ← picardOneScalarExtensionIso_smul c D L,
      SchemeTheory.PointedTorsor.coordinate_smul, habel]
  have ha :
      abelOneMap cL DL ≫ SchemeTheory.PointedTorsor.coordinate
          (G := (groupScheme cL DL).X) (ε ≫ abelOneMap cL DL) =
        modulusAbelMap cL DL ε := by
    simpa only [Category.id_comp] using abelOneMap_pointCoordinate cL DL ε (𝟙 _)
  have heG : eG.hom.hom.hom.hom ≫ eG.inv.hom.hom.hom = 𝟙 _ :=
    congrArg (fun a => a.hom.hom.hom) eG.hom_inv_id
  have hfac : modulusAbelMap cL DL ε ≫ eG.inv.hom.hom.hom =
      qL ≫ SchemeTheory.PointedTorsor.coordinate (G := extendedGroup.X) p₀ := by
    rw [← ha, ← hcoord, Category.assoc, heG, Category.comp_id]
  let a : SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)
      (groupScheme cL DL).X.hom :=
    ⟨(modulusAbelMap cL DL ε).left, Over.w (modulusAbelMap cL DL ε)⟩
  have hmod := ML.regularMapHasModulus_comp DL (groupScheme cL DL) a
    (ML.regularMapHasModulus_abel DL ε) extendedGroup eG.inv
  change ML.regularMapHasModulus DL extendedGroup
    ((commGroupPointEquiv extendedGroup ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      (modulusAbelMap cL DL ε ≫ eG.inv.hom.hom.hom)) at hmod
  rw [hfac] at hmod
  exact ML.regularMapHasModulus_torsorCoordinate_changeBasepoint DL extendedGroup
    (F.obj (picardOne c D)) qL p₀ p hmod

end AlgebraicGeometry.GeneralizedJacobian

open AlgebraicGeometry AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The original full principal-divisor condition implies the geometric
condition over an algebraically closed ground field. The required complement
point is constructed from the curve and is not an additional hypothesis. -/
theorem regularMapHasModulus_geometric
    {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
    [GeometricallyIntegral M.toBase]
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)
    (hmod : M.regularMapHasModulus D G q) :
    geometricRegularMapHasModulus M.toBase D G (Over.homMk q.1 q.2) := by
  obtain ⟨ε⟩ := modulusComplement_point M.toBase D
  intro L fieldL algebraL closedL
  exact M.regularMapHasModulus_scalarExtension D ε G q hmod L

end AlgebraicCurve.CurveModel
