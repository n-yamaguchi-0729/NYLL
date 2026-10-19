/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroForgetfulGroup
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicPresheaf
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The ordinary Picard-zero group sheaf on its existing representing scheme

Normalization at the section and subcanonicity identify the unrigidified
sheaf with the already represented ordinary Picard functor. This supplies the
target of the modulus-forgetting group morphism.
-/

noncomputable section

universe u

open CategoryTheory Opposite NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {J : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

include h in
/-- The actual ordinary zero presheaf already satisfies fppf descent. -/
theorem ordinaryZeroPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (Unrigidified.zeroPresheaf c) := by
  have : (Unrigidified.zeroPresheaf c).IsRepresentable :=
    (h.representableBy.ofIso (Unrigidified.zeroPresheafIso ε).symm).isRepresentable
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Unrigidified.zeroPresheaf c)

/-- Sheafification preserves the ordinary scheme's existing classifying equivalence. -/
def ordinaryZeroSheafRepresentable :
    (ordinaryRelativePicardZeroSheaf c).obj.RepresentableBy (Over.mk J.toBase) :=
  (h.representableBy.ofIso (Unrigidified.zeroPresheafIso ε).symm).ofIso
    (isoSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (ordinaryZeroPresheaf_isSheaf h))

/-- The ordinary zero group sheaf has the same actual carrier. -/
def ordinaryZeroGroupSheafRepresentable :
    ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (Over.mk J.toBase) :=
  (ordinaryZeroSheafRepresentable h).ofIso (ordinaryRelativePicardZeroGroupSheafForgetIso c).symm

/-- The group representation retains the ordinary underlying relative line-bundle class. -/
theorem ordinaryZeroGroupSheafRepresentable_homEquiv
    {T : Over (Spec (CommRingCat.of R))} (f : T ⟶ Over.mk J.toBase) :
    (ordinaryRelativePicardZeroGroupSheafForgetIso c).hom.app (op T)
        ((ordinaryZeroGroupSheafRepresentable h).homEquiv f) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Unrigidified.zeroPresheaf c)).app (op T)
          ((Unrigidified.zeroPresheafIso ε).inv.app (op T)
            (h.representableBy.homEquiv f)) :=
  Iso.inv_hom_id_apply ((ordinaryRelativePicardZeroGroupSheafForgetIso c).app (op T)) _

/-- Tensor product gives the group scheme structure on the ordinary Picard carrier. -/
def ordinaryZeroCommGroupScheme : CommGrp (Over (Spec (CommRingCat.of R))) :=
  SchemeTheory.RepresentedGroups.groupObject (ordinaryRelativePicardZeroGroupSheaf c).obj
    (ordinaryZeroGroupSheafRepresentable h)

/-- The ordinary designation's zero represents the actual neutral Picard group class. -/
theorem ordinaryZeroGroupSheafRepresentable_zero :
    (ordinaryZeroGroupSheafRepresentable h).homEquiv
      (Over.homMk J.zeroSection J.zeroSection_toBase :
        Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk J.toBase) = 1 := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of R)))
  let z : T ⟶ Over.mk J.toBase := Over.homMk J.zeroSection J.zeroSection_toBase
  have hz : (Unrigidified.zeroPresheafIso ε).inv.app (op T)
      (h.representableBy.homEquiv z) =
        (1 : (Unrigidified.zeroCommGrpPresheaf c).obj (op T)) := by
    apply Subtype.ext
    exact Quot.sound (Unrigidified.baseTwist_of_iso h.zero.some)
  have hη := ConcreteCategory.congr_hom (NatTrans.congr_app
    (sheafComposeIso_hom_fac (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (forget CommGrpCat.{u + 1}) (Unrigidified.zeroCommGrpPresheaf c)) (op T))
        (1 : (Unrigidified.zeroCommGrpPresheaf c).obj (op T))
  change (ordinaryRelativePicardZeroGroupSheafForgetIso c).inv.app (op T)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Unrigidified.zeroPresheaf c)).app (op T)
          (1 : (Unrigidified.zeroCommGrpPresheaf c).obj (op T))) =
    ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (Unrigidified.zeroCommGrpPresheaf c)).app (op T)).hom 1 at hη
  change (ordinaryRelativePicardZeroGroupSheafForgetIso c).inv.app (op T)
    ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (Unrigidified.zeroPresheaf c)).app (op T)
        ((Unrigidified.zeroPresheafIso ε).inv.app (op T) (h.representableBy.homEquiv z))) = 1
  rw [hz, hη, map_one]
  rfl

/-- The neutral point of the transported ordinary group is its designated zero section. -/
theorem ordinaryZeroCommGroupScheme_one :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (ordinaryZeroCommGroupScheme h).X) =
      Over.homMk J.zeroSection J.zeroSection_toBase := by
  let e : ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (ordinaryZeroCommGroupScheme h).X :=
    ordinaryZeroGroupSheafRepresentable h
  apply e.homEquiv.injective
  exact ((SchemeTheory.RepresentedGroups.pointEquiv
    (ordinaryRelativePicardZeroGroupSheaf c).obj e
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))).map_one).trans
        (ordinaryZeroGroupSheafRepresentable_zero h).symm

end AlgebraicGeometry.GeneralizedJacobian
