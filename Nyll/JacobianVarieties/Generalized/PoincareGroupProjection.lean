/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareGroupScheme
import Nyll.JacobianVarieties.Generalized.OrdinaryZeroRepresentation
import Nyll.JacobianVarieties.Generalized.PoincareForgetfulComparison

/-!
# The modulus-forgetting morphism of represented group schemes

The actual natural homomorphism of Picard-zero group sheaves determines a
group scheme morphism between the constructed frame scheme and the ordinary
Picard carrier.
-/

noncomputable section

universe u

open CategoryTheory Opposite NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J) (hd : 0 < d)

/-- Forgetting the modulus is a morphism of the constructed commutative group schemes. -/
def poincareModulusGroupProjection :
    poincareModulusCommGroupScheme D h hd ⟶ ordinaryZeroCommGroupScheme h :=
  SchemeTheory.RepresentedGroups.map
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (ordinaryRelativePicardZeroGroupSheaf c).obj
    (poincareModulusPicardZeroGroupRepresentable D h hd)
    (ordinaryZeroGroupSheafRepresentable h)
    (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom

/-- On every test scheme the group morphism forgets precisely the modulus trivialization. -/
theorem poincareModulusGroupProjection_homEquiv
    {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (poincareModulusCommGroupScheme D h hd).X) :
    (ordinaryZeroGroupSheafRepresentable h).homEquiv
      (f ≫ (poincareModulusGroupProjection D h hd).hom.hom.hom) =
        ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom
          ((poincareModulusPicardZeroGroupRepresentable D h hd).homEquiv f) :=
  SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _ _ _ _ f

/-- The represented group morphism is exactly the previously constructed frame projection. -/
theorem poincareModulusGroupProjection_eq :
    (poincareModulusGroupProjection D h hd).hom.hom.hom =
      Over.homMk (poincareFrameQuotient D h hd).hom rfl := by
  let W := (poincareModulusCommGroupScheme D h hd).X
  let m : W ⟶ Over.mk J.toBase := (poincareModulusGroupProjection D h hd).hom.hom.hom
  let p : W ⟶ Over.mk J.toBase := Over.homMk (poincareFrameQuotient D h hd).hom rfl
  let x := (poincareModulusPicardZeroGroupRepresentable D h hd).homEquiv (𝟙 W)
  let y := (poincareFrameTotalRepresentable D h hd).homEquiv (𝟙 W)
  change m = p
  apply (ordinaryZeroGroupSheafRepresentable h).homEquiv.injective
  apply (CategoryTheory.mono_iff_injective
    ((ordinaryRelativePicardZeroGroupSheafForgetIso c).hom.app (op W))).mp inferInstance
  have hm := poincareModulusGroupProjection_homEquiv D h hd (𝟙 W)
  change (ordinaryZeroGroupSheafRepresentable h).homEquiv (𝟙 W ≫ m) =
    ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op W)).hom x at hm
  rw [Category.id_comp] at hm
  rw [hm, ordinaryZeroGroupSheafRepresentable_homEquiv]
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
    (forgetModulusZeroGroupSheaf_forgetIso c (modulusCurveMap D)) (op W)) x
  have hx : (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).hom.app (op W) x =
      (poincareFrameTotalToModulusPicardZero D h).app (op W) y :=
    Iso.inv_hom_id_apply
      ((modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).app (op W)) _
  change (ordinaryRelativePicardZeroGroupSheafForgetIso c).hom.app (op W)
      (((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op W)).hom x) = _
  change (ordinaryRelativePicardZeroGroupSheafForgetIso c).hom.app (op W)
      (((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op W)).hom x) =
    (forgetModulusZeroSheaf c (modulusCurveMap D)).hom.app (op W)
      ((modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).hom.app (op W) x) at hc
  rw [hc, hx]
  have hy := ConcreteCategory.congr_hom (NatTrans.congr_app
    (poincareFrameTotalToModulusPicardZero_forget D h) (op W)) y
  have hp : (poincareFrameTotalToPicard D h).app (op W) y =
      h.representableBy.homEquiv p := by
    have hp' := poincareFrameTotalToPicard_homEquiv D h hd (𝟙 W)
    change (poincareFrameTotalToPicard D h).app (op W) y =
      h.representableBy.homEquiv (𝟙 W ≫ p) at hp'
    rw [Category.id_comp] at hp'
    exact hp'
  change (forgetModulusZeroSheaf c (modulusCurveMap D)).hom.app (op W)
      ((poincareFrameTotalToModulusPicardZero D h).app (op W) y) =
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (Unrigidified.zeroPresheaf c)).app (op W)
        ((Unrigidified.zeroPresheafIso ε).inv.app (op W)
          ((poincareFrameTotalToPicard D h).app (op W) y)) at hy
  rw [hp] at hy
  exact hy

end AlgebraicGeometry.GeneralizedJacobian
