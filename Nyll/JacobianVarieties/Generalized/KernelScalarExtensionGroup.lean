/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.KernelScalarExtensionSheaf
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupSchemeMap
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupBaseChange

/-! # Scalar extension of the genuine kernel group scheme and its actual inclusion -/

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

/-- The restricted kernel group sheaf is represented by the actual pullback
of the identity fibre. -/
def kernelGroupScalarExtensionRepresentable :
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj ⋙
        forget CommGrpCat.{u + 1}).RepresentableBy
      ((Over.pullback (specMap K L)).obj (groupKernelScheme c D)) :=
  SchemeTheory.WeilRestriction.representableByBaseChange (specMap K L)
    (kernelGroupRepresentable c D hd)

/-- The actual base-changed identity fibre with its represented kernel group operation. -/
def kernelGroupScalarExtension : CommGrp (Over (Spec (CommRingCat.of L))) :=
  SchemeTheory.RepresentedGroups.groupObject
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    (kernelGroupScalarExtensionRepresentable c D hd L)

/-- The actual scheme-theoretic kernel commutes with scalar extension as a group scheme. -/
def kernelGroupScalarExtensionIso :
    kernelGroupScalarExtension c D hd L ≅
      kernelGroupScheme (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd :=
  SchemeTheory.RepresentedGroups.iso
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf L
      (modulusAlgebra (D.changeBaseOfIdentity (specMap K L)))).obj
    (kernelGroupScalarExtensionRepresentable c D hd L)
    (kernelGroupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd)
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      CommGrpCat.{u + 1}).mapIso (kernelUnitSheafScalarExtensionIso D L)).symm

/-- The scalar-extended kernel inclusion represents restriction of the actual boundary. -/
def kernelGroupInclusionScalarExtension :
    kernelGroupScalarExtension c D hd L ⟶ groupScalarExtension c D L :=
  SchemeTheory.RepresentedGroups.map
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (kernelGroupScalarExtensionRepresentable c D hd L)
    (groupScalarExtensionRepresentable c D L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom)

/-- This homomorphism is the actual scheme pullback of the original geometric kernel inclusion. -/
theorem kernelGroupInclusionScalarExtension_eq :
    (kernelGroupInclusionScalarExtension c D hd L).hom.hom.hom =
      (Over.pullback (specMap K L)).map (groupKernelInclusion c D) := by
  change SchemeTheory.RepresentedGroups.mapMorphism
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (kernelGroupScalarExtensionRepresentable c D hd L) (groupScalarExtensionRepresentable c D L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom) = _
  exact (SchemeTheory.RepresentedGroups.mapMorphism_baseChange (specMap K L)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (kernelGroupRepresentable c D hd) (groupRepresentable c D)
    (modulusNormBoundarySheaf D).hom).trans
      (congrArg (Over.pullback (specMap K L)).map
        ((kernelGroupInclusion_hom c D hd).symm.trans (kernelGroupInclusion_eq c D hd)))

/-- The actual kernel inclusion classifies the scalar boundary on all parameter schemes. -/
theorem kernelGroupInclusion_homEquiv {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (kernelGroupScheme c D hd).X) :
    (groupRepresentable c D).homEquiv (f ≫ (kernelGroupInclusion c D hd).hom.hom.hom) =
      ((modulusNormBoundarySheaf D).hom.app (op T)).hom
        ((kernelGroupRepresentable c D hd).homEquiv f) :=
  (congrArg (fun m : (kernelGroupScheme c D hd).X ⟶ (groupScheme c D).X =>
    (groupRepresentable c D).homEquiv (f ≫ m)) (kernelGroupInclusion_hom c D hd)).trans
      (SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _
        (kernelGroupRepresentable c D hd) (groupRepresentable c D)
        (modulusNormBoundarySheaf D).hom f)

/-- The explicit underlying kernel comparison morphism. -/
theorem kernelGroupScalarExtensionIso_hom :
    (kernelGroupScalarExtensionIso c D hd L).hom.hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf L
      (modulusAlgebra (D.changeBaseOfIdentity (specMap K L)))).obj
    (kernelGroupScalarExtensionRepresentable c D hd L)
    (kernelGroupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd)
    (kernelUnitSheafScalarExtensionIso D L).inv.hom := rfl

/-- The explicit underlying scalar-extended boundary morphism. -/
theorem kernelGroupInclusionScalarExtension_hom :
    (kernelGroupInclusionScalarExtension c D hd L).hom.hom.hom =
      SchemeTheory.RepresentedGroups.mapMorphism
    ((Over.map (specMap K L)).op ⋙
      (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj)
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (kernelGroupScalarExtensionRepresentable c D hd L) (groupScalarExtensionRepresentable c D L)
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom) := rfl

/-- The canonical kernel and generalized-Jacobian comparisons preserve the actual inclusions. -/
theorem kernelGroup_scalarExtension_square :
    (kernelGroupScalarExtensionIso c D hd L).hom ≫
        kernelGroupInclusion (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd =
      kernelGroupInclusionScalarExtension c D hd L ≫ (groupScalarExtensionIso c D L).hom := by
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
    (kernelGroupScalarExtensionRepresentable c D hd L) (groupScalarExtensionRepresentable c D L)
    (kernelGroupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd)
    (groupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))
    (kernelUnitSheafScalarExtensionIso D L).inv.hom
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv.hom
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusNormBoundarySheaf D).hom)
    (modulusNormBoundarySheaf (D.changeBaseOfIdentity (specMap K L))).hom hs
  apply CommGrp.hom_ext
  exact (congrArg₂ (fun f g => f ≫ g)
    (kernelGroupScalarExtensionIso_hom c D hd L)
    (kernelGroupInclusion_hom (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) hd)).trans
      (h.trans (congrArg₂ (fun f g => f ≫ g)
        (kernelGroupInclusionScalarExtension_hom c D hd L)
        (groupScalarExtensionIso_hom c D L)).symm)

end AlgebraicGeometry.GeneralizedJacobian
