/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupScheme
import Nyll.JacobianVarieties.Generalized.ModulusForgetfulScalarExtension
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupBaseChange

/-! # Scalar extension of the actual generalized-Jacobian projection -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The restricted ordinary group sheaf is represented by the actual ordinary scheme pullback. -/
def ordinaryGroupScalarExtensionRepresentable :
    ((Over.map (specMap K L)).op ⋙
      (ordinaryRelativePicardZeroGroupSheaf c).obj ⋙
        forget CommGrpCat.{u + 1}).RepresentableBy
      ((Over.pullback (specMap K L)).obj (ordinaryGroupScheme c).X) :=
  SchemeTheory.WeilRestriction.representableByBaseChange (specMap K L)
    (ordinaryGroupRepresentable c)

/-- The ordinary Jacobian on its actual scalar-extended carrier. -/
def ordinaryGroupScalarExtension : CommGrp (Over (Spec (CommRingCat.of L))) :=
  SchemeTheory.RepresentedGroups.groupObject
    ((Over.map (specMap K L)).op ⋙ (ordinaryRelativePicardZeroGroupSheaf c).obj)
    (ordinaryGroupScalarExtensionRepresentable c L)

/-- The actual ordinary bundle comparison represents scalar extension as a group isomorphism. -/
def ordinaryGroupScalarExtensionIso :
    ordinaryGroupScalarExtension c L ≅ ordinaryGroupScheme (baseChange K c L) :=
  SchemeTheory.RepresentedGroups.iso
    ((Over.map (specMap K L)).op ⋙ (ordinaryRelativePicardZeroGroupSheaf c).obj)
    (ordinaryRelativePicardZeroGroupSheaf (baseChange K c L)).obj
    (ordinaryGroupScalarExtensionRepresentable c L)
    (ordinaryGroupRepresentable (baseChange K c L))
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      CommGrpCat.{u + 1}).mapIso (ordinaryZeroGroupSheafScalarExtensionIso c L)).symm

/-- The scalar-extended projection represents restriction of the actual forgetful map. -/
def groupProjectionScalarExtension :
    groupScalarExtension c D L ⟶ ordinaryGroupScalarExtension c L :=
  SchemeTheory.RepresentedGroups.map
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    ((Over.map (specMap K L)).op ⋙ (ordinaryRelativePicardZeroGroupSheaf c).obj)
    (groupScalarExtensionRepresentable c D L)
    (ordinaryGroupScalarExtensionRepresentable c L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op
      (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom)

/-- This is exactly the scheme pullback of the original projection. -/
theorem groupProjectionScalarExtension_eq :
    (groupProjectionScalarExtension c D L).hom.hom.hom =
      (Over.pullback (specMap K L)).map (groupProjection c D).hom.hom.hom := by
  change SchemeTheory.RepresentedGroups.mapMorphism
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    ((Over.map (specMap K L)).op ⋙ (ordinaryRelativePicardZeroGroupSheaf c).obj)
    (groupScalarExtensionRepresentable c D L) (ordinaryGroupScalarExtensionRepresentable c L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op
      (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom) = _
  exact (SchemeTheory.RepresentedGroups.mapMorphism_baseChange (specMap K L)
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (ordinaryRelativePicardZeroGroupSheaf c).obj
    (groupRepresentable c D) (ordinaryGroupRepresentable c)
    (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom).trans
      (congrArg (Over.pullback (specMap K L)).map (groupProjection_hom c D).symm)

/-- The actual divisor comparison intertwines the actual forgetful homomorphisms. -/
theorem groupProjection_scalarExtension_square :
    (groupScalarExtensionIso c D L).hom ≫
        groupProjection (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) =
      groupProjectionScalarExtension c D L ≫ (ordinaryGroupScalarExtensionIso c L).hom := by
  let T := (groupScalarExtension c D L).X
  let a := modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L
  let b := ordinaryZeroGroupSheafScalarExtensionIso c L
  let p := (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
    (forgetModulusZeroGroupSheaf c (modulusCurveMap D))
  let p' := forgetModulusZeroGroupSheaf (baseChange K c L)
    (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
  have hs : a.inv ≫ p' = p ≫ b.inv := by
    apply a.inv_comp_eq.mpr
    rw [← Category.assoc, forgetModulusZeroGroupSheaf_divisorScalarExtension,
      Category.assoc, b.hom_inv_id, Category.comp_id]
  let eM := groupScalarExtensionRepresentable c D L
  let eJ := ordinaryGroupScalarExtensionRepresentable c L
  let eJ' := ordinaryGroupRepresentable (baseChange K c L)
  let x := eM.homEquiv (𝟙 T)
  have hx := groupScalarExtensionIso_homEquiv c D L (𝟙 T)
  rw [Category.id_comp] at hx
  have hp0 := SchemeTheory.RepresentedGroups.mapMorphism_homEquiv
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    ((Over.map (specMap K L)).op ⋙ (ordinaryRelativePicardZeroGroupSheaf c).obj) eM eJ
    (Functor.whiskerLeft (Over.map (specMap K L)).op
      (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom) (𝟙 T)
  have hp := (congrArg eJ.homEquiv
    (Category.id_comp (groupProjectionScalarExtension c D L).hom.hom.hom)).symm.trans hp0
  have ho := SchemeTheory.RepresentedGroups.mapMorphism_homEquiv
    ((Over.map (specMap K L)).op ⋙ (ordinaryRelativePicardZeroGroupSheaf c).obj)
    (ordinaryRelativePicardZeroGroupSheaf (baseChange K c L)).obj eJ eJ'
    b.inv.hom (groupProjectionScalarExtension c D L).hom.hom.hom
  have hc := congrArg (fun m :
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).obj
        (modulusPicardZeroGroupSheaf c (modulusCurveMap D)) ⟶
      ordinaryRelativePicardZeroGroupSheaf (baseChange K c L) =>
        (m.hom.app (op T)).hom x) hs
  apply CommGrp.hom_ext
  apply eJ'.homEquiv.injective
  exact (groupProjection_homEquiv (baseChange K c L)
    (D.changeBaseOfIdentity (specMap K L))
    (groupScalarExtensionIso c D L).hom.hom.hom.hom).trans
      ((congrArg (p'.hom.app (op T)).hom hx).trans
        (hc.trans ((congrArg (b.inv.hom.app (op T)).hom hp).symm.trans ho.symm)))

end AlgebraicGeometry.GeneralizedJacobian
