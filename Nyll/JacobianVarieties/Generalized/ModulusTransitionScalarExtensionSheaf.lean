/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.DivisorRestrictionScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionAction
import Nyll.JacobianVarieties.Generalized.PicardOneRestriction

/-! # The actual transition squares for scalar extension of zero and one Picard sheaves -/

noncomputable section

universe u v w

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem unitSquare {B : Type v} [Category.{w} B]
    {A B₀ C D A' B' C' D' : B}
    (eA : A ⟶ A') (eB : B₀ ⟶ B') (eC : C ⟶ C') (eD : D ⟶ D')
    (rAB : A ⟶ B₀) (rAC : A ⟶ C) (rBD : B₀ ⟶ D) (rCD : C ⟶ D)
    (sAB : A' ⟶ B') (sAC : A' ⟶ C') (sBD : B' ⟶ D') (sCD : C' ⟶ D')
    (hAB : eA ≫ sAB = rAB ≫ eB) (hAC : eA ≫ sAC = rAC ≫ eC)
    (hBD : eB ≫ sBD = rBD ≫ eD) (hCD : eC ≫ sCD = rCD ≫ eD)
    (hraw : rAB ≫ rBD = rAC ≫ rCD) :
    eA ≫ (sAB ≫ sBD) = eA ≫ (sAC ≫ sCD) := by
  rw [← Category.assoc, hAB, Category.assoc, hBD, ← Category.assoc, hraw,
    Category.assoc, ← hCD, ← Category.assoc, ← hAC, Category.assoc]

private theorem isoSquare_inv {B : Type v} [Category.{w} B]
    {A B₀ C D : B} (a : A ≅ C) (b : B₀ ≅ D) (f : A ⟶ B₀) (g : C ⟶ D)
    (h : f ≫ b.hom = a.hom ≫ g) : a.inv ≫ f = g ≫ b.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)
  (L : Type u) [Field L] [Algebra K L]

/-- The actual intrinsic degree-one restriction commutes before sheafification. -/
theorem modulusRestrictionOnePresheaf_divisorScalarExtension :
    modulusRestrictionOnePresheaf (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
        (divisorRestrictionScalarMap_square D D' j w L) ≫
      (modulusPicardOne_divisorScalarExtensionIso D' L).hom =
    (modulusPicardOne_divisorScalarExtensionIso D L).hom ≫
      Functor.whiskerLeft (Over.map (specMap K L)).op (modulusRestrictionOnePresheaf c j w) := by
  ext T x
  apply Subtype.ext
  exact divisorScalarExtensionClassesEquiv_restriction D D' j w L T.unop.hom x.val

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- The actual zero-group restriction commutes before sheafification. -/
theorem modulusRestrictionZeroPresheaf_divisorScalarExtension :
    modulusRestrictionZeroPresheaf (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
        (divisorRestrictionScalarMap_square D D' j w L) ≫
      (modulusPicardZeroGroup_divisorScalarExtensionIso D' L).hom =
    (modulusPicardZeroGroup_divisorScalarExtensionIso D L).hom ≫
      Functor.whiskerLeft (Over.map (specMap K L)).op (modulusRestrictionZeroPresheaf c j w) := by
  ext T x
  apply Subtype.ext
  exact divisorScalarExtensionClassesEquiv_restriction D D' j w L T.unop.hom x.val

/-- Scalar extension preserves the same actual intrinsic degree-one sheaf transition. -/
theorem modulusRestrictionOneSheaf_divisorScalarExtension :
    modulusRestrictionOneSheaf (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
        (divisorRestrictionScalarMap_square D D' j w L) ≫
      (modulusPicardOneSheaf_divisorScalarExtensionIso D' L).hom =
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom ≫
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (specMap K L)).map
        (modulusRestrictionOneSheaf c j w) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  let J' := Scheme.fppfTopology.over (Spec (CommRingCat.of L))
  let W := (Functor.whiskeringLeft _ _ (Type (u + 1))).obj (Over.map (specMap K L)).op
  let A := modulusPicardOnePresheaf (baseChange K c L)
    (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
  let B := modulusPicardOnePresheaf (baseChange K c L)
    (modulusCurveMap (D'.changeBaseOfIdentity (specMap K L)))
  let C₀ := modulusPicardOnePresheaf c (modulusCurveMap D)
  let D₀ := modulusPicardOnePresheaf c (modulusCurveMap D')
  let r := modulusRestrictionOnePresheaf c j w
  let s := (modulusRestrictionOneSheaf c j w).hom
  let Q := (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (specMap K L)).obj
    (modulusPicardOneSheaf c (modulusCurveMap D'))
  have hCD : W.map (toSheafify J C₀) ≫ W.map s = W.map r ≫ W.map (toSheafify J D₀) :=
    (W.map_comp _ _).symm.trans
      ((congrArg W.map (toSheafify_modulusRestrictionOneSheaf c j w)).trans (W.map_comp _ _))
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J' _ _ Q.property
  exact unitSquare (toSheafify J' A) (toSheafify J' B)
    (W.map (toSheafify J C₀)) (W.map (toSheafify J D₀))
    (modulusRestrictionOnePresheaf (baseChange K c L)
      (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L))
    (modulusPicardOne_divisorScalarExtensionIso D L).hom
    (modulusPicardOne_divisorScalarExtensionIso D' L).hom (W.map r)
    (modulusRestrictionOneSheaf (baseChange K c L)
      (divisorRestrictionScalarMap D D' j w L)
      (divisorRestrictionScalarMap_square D D' j w L)).hom
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom
    (modulusPicardOneSheaf_divisorScalarExtensionIso D' L).hom.hom (W.map s)
    (toSheafify_modulusRestrictionOneSheaf (baseChange K c L)
      (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L))
    (toSheafify_modulusPicardOne_divisorScalarExtension D L)
    (toSheafify_modulusPicardOne_divisorScalarExtension D' L) hCD
    (modulusRestrictionOnePresheaf_divisorScalarExtension D D' j w L)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- Scalar extension preserves the same actual zero-group sheaf transition. -/
theorem modulusRestrictionZeroSheaf_divisorScalarExtension :
    modulusRestrictionZeroSheaf (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
        (divisorRestrictionScalarMap_square D D' j w L) ≫
      (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D' L).hom =
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom ≫
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
        (modulusRestrictionZeroSheaf c j w) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  let J' := Scheme.fppfTopology.over (Spec (CommRingCat.of L))
  let W := (Functor.whiskeringLeft _ _ CommGrpCat.{u + 1}).obj (Over.map (specMap K L)).op
  let A := modulusPicardZeroGroupPresheaf (baseChange K c L)
    (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
  let B := modulusPicardZeroGroupPresheaf (baseChange K c L)
    (modulusCurveMap (D'.changeBaseOfIdentity (specMap K L)))
  let C₀ := modulusPicardZeroGroupPresheaf c (modulusCurveMap D)
  let D₀ := modulusPicardZeroGroupPresheaf c (modulusCurveMap D')
  let r := modulusRestrictionZeroPresheaf c j w
  let s := (modulusRestrictionZeroSheaf c j w).hom
  let Q := (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).obj
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D'))
  have hCD : W.map (toSheafify J C₀) ≫ W.map s = W.map r ≫ W.map (toSheafify J D₀) :=
    (W.map_comp _ _).symm.trans
      ((congrArg W.map (toSheafify_modulusRestrictionZeroSheaf c j w)).trans (W.map_comp _ _))
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J' _ _ Q.property
  exact unitSquare (toSheafify J' A) (toSheafify J' B)
    (W.map (toSheafify J C₀)) (W.map (toSheafify J D₀))
    (modulusRestrictionZeroPresheaf (baseChange K c L)
      (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L))
    (modulusPicardZeroGroup_divisorScalarExtensionIso D L).hom
    (modulusPicardZeroGroup_divisorScalarExtensionIso D' L).hom (W.map r)
    (modulusRestrictionZeroSheaf (baseChange K c L)
      (divisorRestrictionScalarMap D D' j w L)
      (divisorRestrictionScalarMap_square D D' j w L)).hom
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D' L).hom.hom (W.map s)
    (toSheafify_modulusRestrictionZeroSheaf (baseChange K c L)
      (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L))
    (toSheafify_modulusPicardZeroGroup_divisorScalarExtension D L)
    (toSheafify_modulusPicardZeroGroup_divisorScalarExtension D' L) hCD
    (modulusRestrictionZeroPresheaf_divisorScalarExtension D D' j w L)

/-- The inverse degree-one comparisons give the same scalar-extension square. -/
theorem modulusRestrictionOneSheaf_divisorScalarExtension_inv :
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).inv ≫
      modulusRestrictionOneSheaf (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
        (divisorRestrictionScalarMap_square D D' j w L) =
    (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (specMap K L)).map
        (modulusRestrictionOneSheaf c j w) ≫
      (modulusPicardOneSheaf_divisorScalarExtensionIso D' L).inv :=
  isoSquare_inv _ _ _ _ (modulusRestrictionOneSheaf_divisorScalarExtension D D' j w L)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- The inverse zero-group comparisons give the same scalar-extension square. -/
theorem modulusRestrictionZeroSheaf_divisorScalarExtension_inv :
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv ≫
      modulusRestrictionZeroSheaf (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
        (divisorRestrictionScalarMap_square D D' j w L) =
    (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
        (modulusRestrictionZeroSheaf c j w) ≫
      (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D' L).inv :=
  isoSquare_inv _ _ _ _ (modulusRestrictionZeroSheaf_divisorScalarExtension D D' j w L)

end AlgebraicGeometry.GeneralizedJacobian
