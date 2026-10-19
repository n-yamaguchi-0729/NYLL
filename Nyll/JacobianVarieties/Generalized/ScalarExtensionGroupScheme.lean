/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionSheaf
import Nyll.SchemeTheory.WeilRestriction.Restriction
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupPullbackIso
import Nyll.SchemeTheory.GroupSchemes.AbelianScheme

/-!
# Scalar extension of the constructed generalized Jacobian group scheme

The carrier is the actual scheme pullback. Its group operation classifies tensor
product in the restricted Picard-zero group sheaf. The previously proved whole
divisor comparison identifies this group with the construction over the new field.
-/

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

/-- Restricting the original classifying equivalence is represented by its scheme pullback. -/
def groupScalarExtensionRepresentable :
    ((Over.map (specMap K L)).op ⋙
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
        forget CommGrpCat.{u + 1}).RepresentableBy
      ((Over.pullback (specMap K L)).obj (groupScheme c D).X) :=
  SchemeTheory.WeilRestriction.representableByBaseChange (specMap K L) (groupRepresentable c D)

/-- The actual base-changed carrier with its represented tensor-product group law. -/
def groupScalarExtension : CommGrp (Over (Spec (CommRingCat.of L))) :=
  SchemeTheory.RepresentedGroups.groupObject
    ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
    (groupScalarExtensionRepresentable c D L)

/-- The generalized Jacobian commutes with every field extension as a group scheme. -/
def groupScalarExtensionIso :
    groupScalarExtension c D L ≅
      groupScheme (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) := by
  cases d <;>
    exact SchemeTheory.RepresentedGroups.iso
      ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
      (modulusPicardZeroGroupSheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj
      (groupScalarExtensionRepresentable c D L)
      (groupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))
      ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
        CommGrpCat.{u + 1}).mapIso (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).symm)

/-- The literal pullback of the original group scheme is the generalized
Jacobian of the full extended modulus, with its original group operation. -/
def groupActualScalarExtensionIso :
    (GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D) ≅
      groupScheme (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) := by
  refine ?_ ≪≫ groupScalarExtensionIso c D L
  cases d <;>
    exact SchemeTheory.RepresentedGroups.groupObjectPullbackIso (specMap K L)
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
      (groupRepresentable c D)

/-- The actual scalar-extension comparison as a morphism of the native
pullback objects. Keep its source independent of the transported group law. -/
def groupActualScalarExtensionMap :
    (Over.pullback (specMap K L)).obj (groupScheme c D).X ⟶
      (groupScheme (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))).X :=
  (groupActualScalarExtensionIso c D L).hom.hom.hom.hom

/-- Underlying composition with the scalar-extension comparison can be
computed in the category of schemes over the extended field. -/
theorem groupActualScalarExtensionMap_comp
    {H : CommGrp (Over (Spec (CommRingCat.of L)))}
    (φ : groupScheme (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) ⟶ H) :
    ((groupActualScalarExtensionIso c D L).hom ≫ φ).hom.hom.hom =
      groupActualScalarExtensionMap c D L ≫ φ.hom.hom.hom := rfl

/-- The group comparison sends each represented class by the proved actual modulus comparison. -/
theorem groupScalarExtensionIso_homEquiv {T : Over (Spec (CommRingCat.of L))}
    (f : T ⟶ (groupScalarExtension c D L).X) :
    (groupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))).homEquiv
        (f ≫ (groupScalarExtensionIso c D L).hom.hom.hom.hom) =
      ((modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv.hom.app (op T)).hom
        ((groupScalarExtensionRepresentable c D L).homEquiv f) := by
  cases d <;>
    exact SchemeTheory.RepresentedGroups.mapMorphism_homEquiv
      ((Over.map (specMap K L)).op ⋙ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj)
      (modulusPicardZeroGroupSheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj
      (groupScalarExtensionRepresentable c D L)
      (groupRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))) _ f

end AlgebraicGeometry.GeneralizedJacobian
