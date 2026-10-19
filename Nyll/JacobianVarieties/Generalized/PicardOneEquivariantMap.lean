/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelTorsorDifference
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionTorsor

/-! # Actual equivariant morphisms from the intrinsic Picard-one torsor -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {H : CommGrp (Over (Spec (CommRingCat.of K)))}
  {Q : Over (Spec (CommRingCat.of K))} [ModObj H.X Q]

/-- Actual group morphisms and actual source and target points give regular equivariant maps. -/
def picardOneEquivariantMap (φ : groupScheme c D ⟶ H)
    (p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q) : picardOne c D ⟶ Q :=
  SchemeTheory.PointedTorsor.map φ.hom.hom.hom p q

/-- The actual source point has the specified image. -/
theorem picardOneEquivariantMap_basepoint (φ : groupScheme c D ⟶ H)
    (p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q) :
    p ≫ picardOneEquivariantMap c D φ p q = q :=
  SchemeTheory.PointedTorsor.map_basepoint φ.hom.hom.hom p q

/-- This scheme morphism intertwines the actual tensor action and target action on every test. -/
theorem picardOneEquivariantMap_equivariant (φ : groupScheme c D ⟶ H)
    (p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q)
    {T : Over (Spec (CommRingCat.of K))} (g : T ⟶ (groupScheme c D).X)
    (x : T ⟶ picardOne c D) :
    (g • x) ≫ picardOneEquivariantMap c D φ p q =
      (g ≫ φ.hom.hom.hom) • (x ≫ picardOneEquivariantMap c D φ p q) :=
  SchemeTheory.PointedTorsor.map_equivariant φ.hom.hom.hom p q g x

/-- A source-point value and actual equivariance determine the regular map uniquely. -/
theorem picardOneEquivariantMap_unique (φ : groupScheme c D ⟶ H)
    (p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q)
    (f : picardOne c D ⟶ Q) (hp : p ≫ f = q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K)))
      (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (g • x) ≫ f = (g ≫ φ.hom.hom.hom) • (x ≫ f)) :
    f = picardOneEquivariantMap c D φ p q :=
  SchemeTheory.PointedTorsor.map_unique φ.hom.hom.hom p q f hp hf

/-- Corresponding changes of origins leave the actual equivariant morphism unchanged. -/
theorem picardOneEquivariantMap_changeBasepoint (φ : groupScheme c D ⟶ H)
    (p p' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q) :
    picardOneEquivariantMap c D φ p'
        (p' ≫ picardOneEquivariantMap c D φ p q) =
      picardOneEquivariantMap c D φ p q :=
  SchemeTheory.PointedTorsor.map_changeBasepoint φ.hom.hom.hom p p' q

/-- The map between actual torsors is the given group morphism in actual pointed coordinates. -/
theorem picardOneEquivariantMap_eq_trivializations [IsIso (ModObj.leftSMul H.X Q)]
    (φ : groupScheme c D ⟶ H)
    (p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q) :
    picardOneEquivariantMap c D φ p q =
      (SchemeTheory.PointedTorsor.trivialization p).hom ≫ φ.hom.hom.hom ≫
        (SchemeTheory.PointedTorsor.trivialization q).inv :=
  SchemeTheory.PointedTorsor.map_eq_trivializations φ.hom.hom.hom p q


/-- Scalar extension preserves equivariance after the canonical comparisons
identify the extended group and Picard-one torsor with their actual models.
The same native transported action is used throughout. -/
theorem picardOneMap_scalarExtension_equivariant
    (L : Type u) [Field L] [Algebra K L]
    (φ : groupScheme c D ⟶ H) (f : picardOne c D ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f)) :
    let F := Over.pullback (SmoothProperCurve.specMap K L)
    let cL := SmoothProperCurve.baseChange K c L
    let DL := D.changeBaseOfIdentity (SmoothProperCurve.specMap K L)
    let _ : ModObj (F.obj H.X) (F.obj Q) := F.modObjObj H.X Q
    let _ : ModObj (F.mapCommGrp.obj H).X (F.obj Q) := F.modObjObj H.X Q
    let eG : F.mapCommGrp.obj (groupScheme c D) ≅ groupScheme cL DL :=
      groupActualScalarExtensionIso c D L
    let eP : F.obj (picardOne c D) ≅ picardOne cL DL :=
      picardOneScalarExtensionIso c D L
    ∀ (T : Over (Spec (CommRingCat.of L))) (a : T ⟶ (groupScheme cL DL).X)
      (x : T ⟶ picardOne cL DL),
      (a • x) ≫ (eP.inv ≫ F.map f) =
        (a ≫ (eG.inv.hom.hom.hom ≫ F.map φ.hom.hom.hom)) •
          (x ≫ (eP.inv ≫ F.map f)) := by
  intro F cL DL targetAction targetBundledAction eG eP T a x
  let _ : ModObj (F.obj (groupScheme c D).X) (F.obj (picardOne c D)) :=
    F.modObjObj (groupScheme c D).X (picardOne c D)
  have h := F.map_modObj_equivariant φ.hom.hom.hom f hf T
    (a ≫ eG.inv.hom.hom.hom) (x ≫ eP.inv)
  rw [← Category.assoc, picardOneScalarExtensionIso_inv_smul]
  refine h.trans ?_
  exact congrArg₂ (fun (g : T ⟶ F.obj H.X) (y : T ⟶ F.obj Q) => g • y)
    (Category.assoc a eG.inv.hom.hom.hom (F.map φ.hom.hom.hom))
    (Category.assoc x eP.inv (F.map f))

/-- The actual equivariant map commutes with field extension. Both origins
are transported by the native unit comparison, and the source group and
torsor use their canonical full-modulus comparisons. -/
theorem picardOneEquivariantMap_scalarExtension
    (L : Type u) [Field L] [Algebra K L]
    (φ : groupScheme c D ⟶ H)
    (p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q) :
    let F := Over.pullback (SmoothProperCurve.specMap K L)
    let cL := SmoothProperCurve.baseChange K c L
    let DL := D.changeBaseOfIdentity (SmoothProperCurve.specMap K L)
    let _ : ModObj (F.obj H.X) (F.obj Q) := F.modObjObj H.X Q
    let _ : ModObj (F.mapCommGrp.obj H).X (F.obj Q) := F.modObjObj H.X Q
    let eG : F.mapCommGrp.obj (groupScheme c D) ≅ groupScheme cL DL :=
      groupActualScalarExtensionIso c D L
    let eP : F.obj (picardOne c D) ≅ picardOne cL DL :=
      picardOneScalarExtensionIso c D L
    let φL : groupScheme cL DL ⟶
        F.mapCommGrp.obj H :=
      eG.inv ≫ F.mapCommGrp.map φ
    eP.inv ≫ F.map (picardOneEquivariantMap c D φ p q) =
      picardOneEquivariantMap cL DL φL
        (Functor.LaxMonoidal.ε F ≫ F.map p ≫ eP.hom)
        (Functor.LaxMonoidal.ε F ≫ F.map q) := by
  intro F cL DL targetAction targetBundledAction eG eP φL
  let f := picardOneEquivariantMap c D φ p q
  apply picardOneEquivariantMap_unique cL DL φL
  · change (Functor.LaxMonoidal.ε F ≫ F.map p ≫ eP.hom) ≫
      (eP.inv ≫ F.map f) = Functor.LaxMonoidal.ε F ≫ F.map q
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      ← F.map_comp, picardOneEquivariantMap_basepoint]
  · exact picardOneMap_scalarExtension_equivariant c D L φ f
      (fun _ g y => picardOneEquivariantMap_equivariant c D φ p q g y)

variable (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
  Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))

omit [ModObj H.X Q] in
/-- Coordinates based at the actual Abel point give the actual normalized Abel morphism. -/
theorem abelOneMap_pointCoordinate {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (x ≫ abelOneMap c D) ≫
        SchemeTheory.PointedTorsor.coordinate (G := (groupScheme c D).X)
          (ε ≫ abelOneMap c D) = x ≫ modulusAbelMap c D ε := by
  apply (SchemeTheory.PointedTorsor.coordinate_unique
    (ε ≫ abelOneMap c D) (x ≫ abelOneMap c D) (x ≫ modulusAbelMap c D ε) ?_).symm
  have ht : toUnit T =
      (Over.homMk T.hom (Category.comp_id T.hom) :
        T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
  rw [ht, ← Category.assoc]
  exact modulusAbelMap_smul_basepoint c D ε x

/-- On the actual Abel image, the regular torsor map is the translated group factorization. -/
theorem abelOneMap_equivariantMap (φ : groupScheme c D ⟶ H)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q)
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (x ≫ abelOneMap c D) ≫
        picardOneEquivariantMap c D φ (ε ≫ abelOneMap c D) q =
      ((x ≫ modulusAbelMap c D ε) ≫ φ.hom.hom.hom) • (toUnit T ≫ q) := by
  rw [picardOneEquivariantMap, SchemeTheory.PointedTorsor.map_apply,
    abelOneMap_pointCoordinate c D ε x]

end AlgebraicGeometry.GeneralizedJacobian
