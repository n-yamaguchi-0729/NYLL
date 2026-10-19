/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionAction
import Nyll.JacobianVarieties.Generalized.ModulusClosedFieldPoints
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionClasses
import Nyll.JacobianVarieties.Generalized.ModulusAbelMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelTorsorDifference
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupSchemeMap

/-! # Actual pointed Abel maps on scalar-extended group points -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Scalar extension preserves the actual positive Abel class for the full divisor. -/
theorem divisorScalarExtensionClassesEquiv_abelPoint
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    divisorScalarExtensionClassesEquiv c D L T.hom
      (modulusAbelPointClass (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) x) =
      modulusAbelPointClass c (modulusCurveMap D) (divisorScalarExtensionPoint c D L x) :=
  congrArg Subtype.val (modulusAbelOnePresheafMap_divisorScalarExtension c D L x)

private theorem abelZeroClass_val
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (modulusAbelZeroClass c (modulusCurveMap D) ε x).val =
      modulusAbelPointClass c (modulusCurveMap D) x /
        modulusAbelPointClass c (modulusCurveMap D)
          (Over.homMk T.hom (Category.comp_id _) ≫ ε) := by
  have h := congrArg Subtype.val (modulusAbelZeroClass_action c D ε x)
  change (modulusAbelZeroClass c (modulusCurveMap D) ε x).val *
      modulusAbelPointClass c (modulusCurveMap D)
        (Over.homMk T.hom (Category.comp_id _) ≫ ε) =
      modulusAbelPointClass c (modulusCurveMap D) x at h
  exact eq_div_iff_mul_eq'.mpr h

/-- The raw zero-class comparison preserves the actual point-minus-basepoint family. -/
theorem modulusAbelZeroClass_divisorScalarExtension
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (modulusPicardZeroGroup_divisorScalarExtensionIso (c := c) D L).hom.app (op T)
      (modulusAbelZeroClass (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
        (modulusBasepointScalarExtension c D L ε) x) =
      modulusAbelZeroClass c (modulusCurveMap D) ε (divisorScalarExtensionPoint c D L x) := by
  apply Subtype.ext
  change divisorScalarExtensionClassesEquiv c D L T.hom
      (modulusAbelZeroClass (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
        (modulusBasepointScalarExtension c D L ε) x).val =
      (modulusAbelZeroClass c (modulusCurveMap D) ε
        (divisorScalarExtensionPoint c D L x)).val
  rw [abelZeroClass_val, abelZeroClass_val, map_div,
    divisorScalarExtensionClassesEquiv_abelPoint,
    divisorScalarExtensionClassesEquiv_abelPoint, modulusBasepointScalarExtension_project]
  rfl

/-- The group-sheaf comparison preserves the actual pointed Abel family. -/
theorem modulusAbelZeroSheafClass_divisorScalarExtension
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)
      (modulusAbelZeroSheafClass (baseChange K c L)
        (D.changeBaseOfIdentity (specMap K L)) (modulusBasepointScalarExtension c D L ε) x) =
      modulusAbelZeroSheafClass c D ε (divisorScalarExtensionPoint c D L x) := by
  let z := modulusAbelZeroClass (baseChange K c L)
    (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
    (modulusBasepointScalarExtension c D L ε) x
  have h := congrArg (fun α => (α.app (op T)).hom z)
    (toSheafify_modulusPicardZeroGroup_divisorScalarExtension (c := c) D L)
  change (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
        (modulusPicardZeroGroupPresheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))))).app (op T) z) =
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app
        (op ((Over.map (specMap K L)).obj T))
          ((modulusPicardZeroGroup_divisorScalarExtensionIso (c := c) D L).hom.app (op T) z) at h
  exact h.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app
        (op ((Over.map (specMap K L)).obj T)))
      (modulusAbelZeroClass_divisorScalarExtension c D L ε x))

/-- The actual scalar-extension comparison on group-valued points of every test scheme. -/
def groupScalarExtensionPointEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (groupScheme (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))).X) ≃*
      ((Over.map (specMap K L)).obj T ⟶ (groupScheme c D).X) :=
  (pointEquiv (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) T).trans
    (((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      CommGrpCat.{u + 1}).mapIso
        (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L)).app
          (op T)).commGroupIsoToMulEquiv
    |>.trans (pointEquiv c D ((Over.map (specMap K L)).obj T)).symm

/-- On a closed extension field, the actual point comparison transports the
same raw rigidified class through the full divisor comparison. -/
theorem groupScalarExtensionPointEquiv_rigidifiedClass [IsAlgClosed L]
    (z : modulusPicardZeroSubgroup (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
        (Over.mk (𝟙 (Spec (CommRingCat.of L))))) :
    pointEquiv c D ((Over.map (specMap K L)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of L)))))
      (groupScalarExtensionPointEquiv c D L (Over.mk (𝟙 (Spec (CommRingCat.of L))))
        (rigidifiedZeroClassPointEquiv (baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)) z)) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app
          (op ((Over.map (specMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L))))))
        ((modulusPicardZeroGroup_divisorScalarExtensionIso (c := c) D L).hom.app
          (op (Over.mk (𝟙 (Spec (CommRingCat.of L))))) z) := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let e := pointEquiv c D ((Over.map (specMap K L)).obj T)
  let eL := pointEquiv (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) T
  let σ := (((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
    CommGrpCat.{u + 1}).mapIso
      (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L)).app
        (op T)).commGroupIsoToMulEquiv
  change e (e.symm (σ (eL (rigidifiedZeroClassPointEquiv (baseChange K c L)
    (D.changeBaseOfIdentity (specMap K L)) z)))) = _
  refine (e.apply_symm_apply _).trans ?_
  rw [rigidifiedZeroClassPointEquiv_classifies]
  exact congrArg (fun α => (α.app (op T)).hom z)
    (toSheafify_modulusPicardZeroGroup_divisorScalarExtension (c := c) D L)

private theorem pointEquiv_apply_eq {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (groupScheme c D).X) :
    pointEquiv c D T x = (groupRepresentable c D).homEquiv x := by
  cases d <;> rfl

/-- The actual pointed Abel morphism is compatible with every field extension. -/
theorem groupScalarExtensionPointEquiv_modulusAbelMap
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    groupScalarExtensionPointEquiv c D L T
      (x ≫ modulusAbelMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))
        (modulusBasepointScalarExtension c D L ε)) =
      divisorScalarExtensionPoint c D L x ≫ modulusAbelMap c D ε := by
  let e := pointEquiv c D ((Over.map (specMap K L)).obj T)
  let eL := pointEquiv (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) T
  let σ : (modulusPicardZeroGroupSheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj.obj (op T) →*
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.obj
        (op ((Over.map (specMap K L)).obj T)) :=
    ((modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)).hom
  change e.symm (σ (eL
    (x ≫ modulusAbelMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))
      (modulusBasepointScalarExtension c D L ε)))) = _
  apply e.symm_apply_eq.mpr
  have hx : eL (x ≫ modulusAbelMap (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) (modulusBasepointScalarExtension c D L ε)) =
      modulusAbelZeroSheafClass (baseChange K c L)
        (D.changeBaseOfIdentity (specMap K L)) (modulusBasepointScalarExtension c D L ε) x :=
    (pointEquiv_apply_eq _ _ _).trans (modulusAbelMap_classifies _ _ _ _)
  have hy : e (divisorScalarExtensionPoint c D L x ≫ modulusAbelMap c D ε) =
      modulusAbelZeroSheafClass c D ε (divisorScalarExtensionPoint c D L x) :=
    (pointEquiv_apply_eq c D _).trans (modulusAbelMap_classifies c D ε _)
  exact (congrArg σ hx).trans
    ((modulusAbelZeroSheafClass_divisorScalarExtension c D L ε x).trans hy.symm)


/-- The native group-scheme pullback comparison induces the same adjunction
on every test scheme as the constructed scalar-extension point equivalence. -/
theorem groupScalarExtensionPointEquiv_actualIso
    {T : Over (Spec (CommRingCat.of L))}
    (f : T ⟶ ((GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D)).X) :
    groupScalarExtensionPointEquiv c D L T
        (f ≫ (groupActualScalarExtensionIso c D L).hom.hom.hom.hom) =
      ((Over.mapPullbackAdj (specMap K L)).homEquiv T (groupScheme c D).X).symm f := by
  let e := pointEquiv c D ((Over.map (specMap K L)).obj T)
  let eL := pointEquiv (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) T
  let σ := (((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
    CommGrpCat.{u + 1}).mapIso
      (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L)).app
        (op T)).commGroupIsoToMulEquiv
  have hb : (groupScalarExtensionRepresentable c D L).homEquiv f =
      e (((Over.mapPullbackAdj (specMap K L)).homEquiv T (groupScheme c D).X).symm f) := by
    change (groupRepresentable c D).homEquiv
      (((Over.mapPullbackAdj (specMap K L)).homEquiv T (groupScheme c D).X).symm f) = _
    exact (pointEquiv_apply_eq c D _).symm
  have hf : eL (f ≫ (groupActualScalarExtensionIso c D L).hom.hom.hom.hom) =
      σ.symm
        (e (((Over.mapPullbackAdj (specMap K L)).homEquiv T (groupScheme c D).X).symm f)) := by
    rw [groupActualScalarExtensionIso_hom]
    exact (pointEquiv_apply_eq _ _ _).trans
      ((groupScalarExtensionIso_homEquiv c D L f).trans (congrArg σ.symm hb))
  change e.symm (σ (eL
    (f ≫ (groupActualScalarExtensionIso c D L).hom.hom.hom.hom))) = _
  exact (congrArg (fun z => e.symm (σ z)) hf).trans
    ((congrArg e.symm (σ.apply_symm_apply _)).trans (e.symm_apply_apply _))

/-- The pointed Abel morphism commutes with the native pullback group scheme,
including its actual group structure, for every parameter scheme. -/
theorem groupActualScalarExtensionIso_modulusAbelMap
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    ((Over.mapPullbackAdj (specMap K L)).homEquiv T (groupScheme c D).X)
        (divisorScalarExtensionPoint c D L x ≫ modulusAbelMap c D ε) ≫
      (groupActualScalarExtensionIso c D L).hom.hom.hom.hom =
        x ≫ modulusAbelMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))
          (modulusBasepointScalarExtension c D L ε) := by
  apply (groupScalarExtensionPointEquiv c D L T).injective
  exact (groupScalarExtensionPointEquiv_actualIso c D L _).trans
    ((((Over.mapPullbackAdj (specMap K L)).homEquiv T (groupScheme c D).X).symm_apply_apply
      _).trans (groupScalarExtensionPointEquiv_modulusAbelMap c D L ε x).symm)


/-- Extending a group morphism and the Abel map gives the same morphism as
extending their composite. The comparison uses the native pullback group
structure on the target and the full relative divisor on the source. -/
theorem groupActualScalarExtensionIso_modulusAbelMap_comp
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) (φ : groupScheme c D ⟶ G)
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (x ≫ modulusAbelMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))
        (modulusBasepointScalarExtension c D L ε)) ≫
      ((groupActualScalarExtensionIso c D L).inv ≫
        (GroupSchemes.baseChange (specMap K L)).map φ).hom.hom.hom =
      ((Over.mapPullbackAdj (specMap K L)).homEquiv T G.X)
        ((divisorScalarExtensionPoint c D L x ≫ modulusAbelMap c D ε) ≫
          φ.hom.hom.hom) := by
  let e := groupActualScalarExtensionIso c D L
  let a := ((Over.mapPullbackAdj (specMap K L)).homEquiv T (groupScheme c D).X)
    (divisorScalarExtensionPoint c D L x ≫ modulusAbelMap c D ε)
  have ha : a ≫ e.hom.hom.hom.hom =
      x ≫ modulusAbelMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))
        (modulusBasepointScalarExtension c D L ε) :=
    groupActualScalarExtensionIso_modulusAbelMap c D L ε x
  have he : e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f :
      (GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D) ⟶
        (GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D) =>
          f.hom.hom.hom) e.hom_inv_id
  change (x ≫ modulusAbelMap (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) (modulusBasepointScalarExtension c D L ε)) ≫
    (e.inv.hom.hom.hom ≫ (Over.pullback (specMap K L)).map φ.hom.hom.hom) = _
  refine (congrArg (· ≫ (e.inv.hom.hom.hom ≫
      (Over.pullback (specMap K L)).map φ.hom.hom.hom)) ha.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (a ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Over.pullback (specMap K L)).map φ.hom.hom.hom) he).trans
      (Category.id_comp _)))).trans ?_
  exact ((Over.mapPullbackAdj (specMap K L)).homEquiv_naturality_right
    (divisorScalarExtensionPoint c D L x ≫ modulusAbelMap c D ε) φ.hom.hom.hom).symm

end AlgebraicGeometry.GeneralizedJacobian
