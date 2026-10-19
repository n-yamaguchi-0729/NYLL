/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.KernelScalarExtensionSheaf
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupSchemeMap
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupBaseChange

/-! # Scalar extension of the norm-open group and its actual scalar boundary -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve SchemeTheory.Affine

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)
  (L : Type u) [Field L] [Algebra K L]

/-- The restricted norm-open group sheaf is represented by the actual scheme pullback. -/
def modulusNormGroupScalarExtensionRepresentable :
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj ⋙
        forget CommGrpCat.{u + 1}).RepresentableBy
      ((Over.pullback (specMap K L)).obj (modulusUnitQuotient D hd).X) :=
  SchemeTheory.WeilRestriction.representableByBaseChange (specMap K L)
    (modulusUnitQuotientRepresentable D hd)

/-- The actual base-changed norm-open carrier with its represented group operation. -/
def modulusNormGroupScalarExtension : CommGrp (Over (Spec (CommRingCat.of L))) :=
  SchemeTheory.RepresentedGroups.groupObject
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    (modulusNormGroupScalarExtensionRepresentable c D hd L)

/-- The concrete norm-open group commutes with scalar extension. -/
def modulusNormGroupScalarExtensionIso :
    modulusNormGroupScalarExtension c D hd L ≅
      modulusUnitQuotient (D.changeBaseOfIdentity (specMap K L)) hd :=
  SchemeTheory.RepresentedGroups.iso
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf L
      (modulusAlgebra (D.changeBaseOfIdentity (specMap K L)))).obj
    (modulusNormGroupScalarExtensionRepresentable c D hd L)
    (modulusUnitQuotientRepresentable (D.changeBaseOfIdentity (specMap K L)) hd)
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      CommGrpCat.{u + 1}).mapIso (kernelUnitSheafScalarExtensionIso D L)).symm

/-- The scalar-extended norm boundary represents restriction of the actual scalar boundary. -/
def modulusNormBoundaryScalarExtension :
    modulusNormGroupScalarExtension c D hd L ⟶ groupScalarExtension c D L :=
  SchemeTheory.RepresentedGroups.map
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (modulusNormGroupScalarExtensionRepresentable c D hd L)
    (groupScalarExtensionRepresentable c D L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom)

/-- This homomorphism is the actual scheme pullback of the original scalar boundary. -/
theorem modulusNormBoundaryScalarExtension_eq :
    (modulusNormBoundaryScalarExtension c D hd L).hom.hom.hom =
      (Over.pullback (specMap K L)).map (modulusNormBoundary c D hd).hom.hom.hom := by
  change SchemeTheory.RepresentedGroups.mapMorphism
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (modulusNormGroupScalarExtensionRepresentable c D hd L)
    (groupScalarExtensionRepresentable c D L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom) = _
  exact (SchemeTheory.RepresentedGroups.mapMorphism_baseChange (specMap K L)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (modulusUnitQuotientRepresentable D hd) (groupRepresentable c D)
    (modulusNormBoundarySheaf D).hom).trans
      (congrArg (Over.pullback (specMap K L)).map
        (modulusNormBoundary_hom c D hd).symm)

/-- The explicit underlying kernel comparison morphism. -/
theorem modulusNormGroupScalarExtensionIso_hom :
    (modulusNormGroupScalarExtensionIso c D hd L).hom.hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf L
      (modulusAlgebra (D.changeBaseOfIdentity (specMap K L)))).obj
    (modulusNormGroupScalarExtensionRepresentable c D hd L)
    (modulusUnitQuotientRepresentable (D.changeBaseOfIdentity (specMap K L)) hd)
    (kernelUnitSheafScalarExtensionIso D L).inv.hom := rfl

/-- The explicit underlying scalar-extended boundary morphism. -/
theorem modulusNormBoundaryScalarExtension_hom :
    (modulusNormBoundaryScalarExtension c D hd L).hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (modulusNormGroupScalarExtensionRepresentable c D hd L)
    (groupScalarExtensionRepresentable c D L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom) := rfl

/-- The norm-open and generalized-Jacobian comparisons preserve the actual scalar boundaries. -/
theorem modulusNormBoundary_scalarExtension_square :
    (modulusNormGroupScalarExtensionIso c D hd L).hom ≫
        modulusNormBoundary (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd =
      modulusNormBoundaryScalarExtension c D hd L ≫ (groupScalarExtensionIso c D L).hom := by
  have hs : (kernelUnitSheafScalarExtensionIso D L).inv.hom ≫
      (modulusNormBoundarySheaf (D.changeBaseOfIdentity (specMap K L))).hom =
    Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom ≫
      (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv.hom :=
    congrArg (fun m :
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).obj
        (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)) ⟶
      modulusPicardZeroGroupSheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) => m.hom)
      (kernelUnitSheafScalarExtensionIso_inv_boundary D L)
  have h := SchemeTheory.RepresentedGroups.mapMorphism_square
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf L
      (modulusAlgebra (D.changeBaseOfIdentity (specMap K L)))).obj
    (modulusPicardZeroGroupSheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj
    (modulusNormGroupScalarExtensionRepresentable c D hd L)
    (groupScalarExtensionRepresentable c D L)
    (modulusUnitQuotientRepresentable (D.changeBaseOfIdentity (specMap K L)) hd)
    (groupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))
    (kernelUnitSheafScalarExtensionIso D L).inv.hom
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv.hom
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom)
    (modulusNormBoundarySheaf (D.changeBaseOfIdentity (specMap K L))).hom hs
  apply CommGrp.hom_ext
  exact (congrArg₂ (fun f g => f ≫ g)
    (modulusNormGroupScalarExtensionIso_hom c D hd L)
    (modulusNormBoundary_hom (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd)).trans
      (h.trans (congrArg₂ (fun f g => f ≫ g)
        (modulusNormBoundaryScalarExtension_hom c D hd L)
        (groupScalarExtensionIso_hom c D L)).symm)

end AlgebraicGeometry.GeneralizedJacobian
