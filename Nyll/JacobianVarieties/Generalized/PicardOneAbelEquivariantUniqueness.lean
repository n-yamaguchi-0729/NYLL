/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneEquivariantMap
import Nyll.JacobianVarieties.Generalized.PicardOneTransitionFunctoriality
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionTorsor
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupScheme
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelOneScalarExtension
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap
import Nyll.SchemeTheory.CategoryTheory.EquivariantScalarTowerComparison
import Nyll.SchemeTheory.Morphisms.OverPullbackDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-! # Actual torsor and group morphisms are jointly determined by the Abel morphism -/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

private abbrev comp_obj_hom
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A ⥤ B) (G : B ⥤ C) {X : A} {Y : C} (f : Y ⟶ (F ⋙ G).obj X) :
    Y ⟶ G.obj (F.obj X) := f

/-- Keep the underlying morphism of a transported group map in the functor's
native object types. -/
private abbrev mapCommGrp_underlying
    {A B : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    (F : A ⥤ B) [F.Braided] {G H : CommGrp A}
    (f : F.mapCommGrp.obj G ⟶ F.mapCommGrp.obj H) :
    F.obj G.X ⟶ F.obj H.X := f.hom.hom.hom

private theorem map_eq_of_iso_transport
    {A B : Type u} [Category.{v} A] [Category.{v} B] (F : A ⥤ B)
    {X Y Z : A} {P R S T : B}
    (i : X ≅ Y) (j : F.obj Y ≅ P) (e : F.obj X ≅ R) (m : R ≅ S)
    (φ : S ⟶ T) (t : T ⟶ F.obj Z) (f : Y ⟶ Z)
    (h : (j.symm ≪≫ F.mapIso i.symm ≪≫ e ≪≫ m).hom ≫ φ ≫ t =
      j.inv ≫ F.map f) :
    F.map (i.hom ≫ f) = e.hom ≫ (m.hom ≫ φ) ≫ t := by
  have h' := congrArg (fun z => (F.map i.hom ≫ j.hom) ≫ z) h
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc] at h'
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp] at h'
  simpa only [F.map_comp, Category.assoc] using h'.symm

private theorem commGrp_tower_underlying
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (F : A ⥤ C) [F.Braided]
    (F₁ : A ⥤ B) [F₁.Braided] (F₂ : B ⥤ C) [F₂.Braided]
    (e : F ≅ F₁ ⋙ F₂) (G H : CommGrp A)
    (mL : F₁.mapCommGrp.obj G ⟶ F₁.mapCommGrp.obj H)
    (mM : F.mapCommGrp.obj G ⟶ F.mapCommGrp.obj H)
    (h :
      let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
      F₂.mapCommGrp.map mL = (eB.app G).inv ≫ mM ≫ (eB.app H).hom) :
    F₂.map (mapCommGrp_underlying F₁ mL) =
      e.inv.app G.X ≫ mapCommGrp_underlying F mM ≫ e.hom.app H.X := by
  have h' := congrArg (fun f => f.hom.hom.hom) h
  change F₂.map (mapCommGrp_underlying F₁ mL) =
    (𝟙 _ ≫ e.inv.app G.X) ≫ mapCommGrp_underlying F mM ≫ (e.hom.app H.X ≫ 𝟙 _) at h'
  exact h'.trans (congrArg₂
    (fun (a : (F₁ ⋙ F₂).obj G.X ⟶ F.obj G.X)
      (b : F.obj H.X ⟶ (F₁ ⋙ F₂).obj H.X) => a ≫ mapCommGrp_underlying F mM ≫ b)
    (Category.id_comp (e.inv.app G.X)) (Category.comp_id (e.hom.app H.X)))

/-- Express field-point descent using the same scalar-map objects as the curve
comparison APIs, retaining those objects throughout the tower compatibility. -/
private theorem overPullback_specMap_field_map_value
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    {X Y : Over (Spec (CommRingCat.of K))}
    (mL : (Over.pullback (specMap K L)).obj X ⟶ (Over.pullback (specMap K L)).obj Y)
    (mM : (Over.pullback (specMap K M)).obj X ⟶ (Over.pullback (specMap K M)).obj Y)
    (hcompat : ∀ [Algebra L M] [IsScalarTower K L M],
      let sKL := specMap K L
      let sLM := specMap L M
      let sKM := specMap K M
      let w : sLM ≫ sKL = sKM := specMap_scalarTower_comp K L M
      let e : Over.pullback sKM ≅ Over.pullback sKL ⋙ Over.pullback sLM :=
        (eqToIso (congrArg
          (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
            Over.pullbackComp sLM sKL
      (Over.pullback sLM).map mL = e.inv.app X ≫ mM ≫ e.hom.app Y)
    (x : Spec (CommRingCat.of M) ⟶ Limits.pullback X.hom (specMap K L))
    (y : Spec (CommRingCat.of M) ⟶ Limits.pullback X.hom (specMap K M))
    (hy : y ≫ Limits.pullback.snd X.hom (specMap K M) = 𝟙 _)
    (hxy : x ≫ Limits.pullback.fst X.hom (specMap K L) =
      y ≫ Limits.pullback.fst X.hom (specMap K M)) :
    x ≫ mL.left ≫ Limits.pullback.fst Y.hom (specMap K L) =
      y ≫ mM.left ≫ Limits.pullback.fst Y.hom (specMap K M) := by
  refine overPullback_map_value_of_tower_compat
    (specMap K L) (specMap K M) mL mM ?_ x y hy hxy
  intro a h
  obtain ⟨algebraLM, towerKLM, ha⟩ := exists_algebra_tower_of_spec_triangle a h
  exact overPullback_tower_compat_of_eq (specMap K L) (specMap K M) mL mM
    (specMap L M) a (specMap_scalarTower_comp K L M) h ha hcompat

/-- Field-point descent for morphisms of transported commutative groups.
The conversion to underlying scheme maps is performed with abstract groups. -/
private theorem commGrp_specMap_field_map_value
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    {G H : CommGrp (Over (Spec (CommRingCat.of K)))}
    (mL : (Over.pullback (specMap K L)).mapCommGrp.obj G ⟶
      (Over.pullback (specMap K L)).mapCommGrp.obj H)
    (mM : (Over.pullback (specMap K M)).mapCommGrp.obj G ⟶
      (Over.pullback (specMap K M)).mapCommGrp.obj H)
    (hcompat : ∀ [Algebra L M] [IsScalarTower K L M],
      let sKL := specMap K L
      let sLM := specMap L M
      let sKM := specMap K M
      let w : sLM ≫ sKL = sKM := specMap_scalarTower_comp K L M
      let e : Over.pullback sKM ≅ Over.pullback sKL ⋙ Over.pullback sLM :=
        (eqToIso (congrArg
          (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
            Over.pullbackComp sLM sKL
      let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
      (Over.pullback sLM).mapCommGrp.map mL = (eB.app G).inv ≫ mM ≫ (eB.app H).hom)
    (x : Spec (CommRingCat.of M) ⟶ Limits.pullback G.X.hom (specMap K L))
    (y : Spec (CommRingCat.of M) ⟶ Limits.pullback G.X.hom (specMap K M))
    (hy : y ≫ Limits.pullback.snd G.X.hom (specMap K M) = 𝟙 _)
    (hxy : x ≫ Limits.pullback.fst G.X.hom (specMap K L) =
      y ≫ Limits.pullback.fst G.X.hom (specMap K M)) :
    x ≫ (mapCommGrp_underlying (Over.pullback (specMap K L)) mL).left ≫
        Limits.pullback.fst H.X.hom (specMap K L) =
      y ≫ (mapCommGrp_underlying (Over.pullback (specMap K M)) mM).left ≫
        Limits.pullback.fst H.X.hom (specMap K M) := by
  apply overPullback_specMap_field_map_value (K := K) (L := L) (M := M)
    (X := G.X) (Y := H.X)
    (mapCommGrp_underlying (Over.pullback (specMap K L)) mL)
    (mapCommGrp_underlying (Over.pullback (specMap K M)) mM) ?_ x y hy hxy
  intro algebraLM tower sKL sLM sKM w e
  exact commGrp_tower_underlying (Over.pullback sKM) (Over.pullback sKL)
    (Over.pullback sLM) e G H mL mM hcompat

private theorem natTrans_comp_action
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C]
    (F : A ⥤ C) [F.Monoidal]
    (F₁ : A ⥤ B) [F₁.Monoidal] (F₂ : B ⥤ C) [F₂.Monoidal]
    (G P : A) [MonObj G] [ModObj G P] (τ : F ⟶ F₁ ⋙ F₂)
    {T : C} (a : T ⟶ F.obj G) (x : T ⟶ F.obj P) :
    (lift a x ≫ (Functor.LaxMonoidal.μ F G P ≫ F.map γ[G, P])) ≫ τ.app P =
      lift (show T ⟶ F₂.obj (F₁.obj G) from a ≫ τ.app G)
        (show T ⟶ F₂.obj (F₁.obj P) from x ≫ τ.app P) ≫
      (Functor.LaxMonoidal.μ F₂ (F₁.obj G) (F₁.obj P) ≫
        F₂.map (Functor.LaxMonoidal.μ F₁ G P ≫ F₁.map γ[G, P])) := by
  exact F.natTrans_comp_modObj_smul G P F₁ F₂ τ a x

private theorem pullback_tower_action
    {S T U : Scheme.{u}} (s : T ⟶ S) (t : U ⟶ T) (r : U ⟶ S)
    (e : Over.pullback r ≅ Over.pullback s ⋙ Over.pullback t)
    (H : CommGrp (Over S)) (Q : Over S) [ModObj H.X Q] :
    let FKL := Over.pullback s
    let FLM := Over.pullback t
    let FKM := Over.pullback r
    let HL := FKL.mapCommGrp.obj H
    let HM := FKM.mapCommGrp.obj H
    let _actionL : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _actionM : ModObj HM.X (FKM.obj Q) := FKM.modObjObj H.X Q
    let HLM := FLM.mapCommGrp.obj HL
    let _actionLM : ModObj HLM.X (FLM.obj (FKL.obj Q)) := FLM.modObjObj HL.X (FKL.obj Q)
    let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    let b : HM ⟶ HLM := comp_obj_hom FKL.mapCommGrp FLM.mapCommGrp (eB.app H).hom
    let p : FKM.obj Q ⟶ FLM.obj (FKL.obj Q) := comp_obj_hom FKL FLM (e.hom.app Q)
    ∀ (actionM' : ModObj HM.X (FKM.obj Q)) (_ : actionM' = _actionM)
      (actionLM' : ModObj HLM.X (FLM.obj (FKL.obj Q))) (_ : actionLM' = _actionLM)
      (b' : HM ⟶ HLM) (_ : b' = b)
      (p' : FKM.obj Q ⟶ FLM.obj (FKL.obj Q)) (_ : p' = p),
    let _ : ModObj HM.X (FKM.obj Q) := actionM'
    let _ : ModObj HLM.X (FLM.obj (FKL.obj Q)) := actionLM'
    ∀ (V : Over U) (a : V ⟶ HM.X) (x : V ⟶ FKM.obj Q),
      (a • x) ≫ p' = (a ≫ b'.hom.hom.hom) • (x ≫ p') := by
  intro FKL FLM FKM HL HM actionL actionM HLM actionLM eB b p
  rintro actionM' rfl actionLM' rfl b' rfl p' rfl
  intro actionM' actionLM' V a x
  have heB : b.hom.hom.hom = e.hom.app H.X := by
    change e.hom.app H.X ≫ 𝟙 _ = e.hom.app H.X
    exact Category.comp_id _
  rw [heB]
  change (lift a x ≫ (Functor.LaxMonoidal.μ FKM H.X Q ≫ FKM.map γ[H.X, Q])) ≫
      e.hom.app Q =
    lift (show V ⟶ FLM.obj (FKL.obj H.X) from a ≫ e.hom.app H.X)
      (show V ⟶ FLM.obj (FKL.obj Q) from x ≫ e.hom.app Q) ≫
    (Functor.LaxMonoidal.μ FLM (FKL.obj H.X) (FKL.obj Q) ≫
      FLM.map (Functor.LaxMonoidal.μ FKL H.X Q ≫ FKL.map γ[H.X, Q]))
  exact natTrans_comp_action FKM FKL FLM H.X Q e.hom a x


variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  {H : CommGrp (Over (Spec (CommRingCat.of K)))}
  {Q : Over (Spec (CommRingCat.of K))} [ModObj H.X Q]
  [IsIso (ModObj.leftSMul H.X Q)]

/-- Target coordinates turn the actual Abel factorization through the torsor into the
actual pointed group factorization. -/
theorem abelOneMap_equivariantMap_coordinate (φ : groupScheme c D ⟶ H)
    (q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q) :
    (abelOneMap c D ≫ picardOneEquivariantMap c D φ (ε ≫ abelOneMap c D) q) ≫
        SchemeTheory.PointedTorsor.coordinate q =
      modulusAbelMap c D ε ≫ φ.hom.hom.hom := by
  let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D := ε ≫ abelOneMap c D
  have hc : abelOneMap c D ≫ SchemeTheory.PointedTorsor.coordinate
      (G := (groupScheme c D).X) p = modulusAbelMap c D ε := by
    simpa only [Category.id_comp] using abelOneMap_pointCoordinate c D ε (𝟙 _)
  have hm : picardOneEquivariantMap c D φ p q ≫
      SchemeTheory.PointedTorsor.coordinate q =
        SchemeTheory.PointedTorsor.coordinate p ≫ φ.hom.hom.hom :=
    SchemeTheory.PointedTorsor.map_coordinate φ.hom.hom.hom p q
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => abelOneMap c D ≫ a) hm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ φ.hom.hom.hom) hc)))

variable [IsSeparated H.X.hom]

include ε in
/-- Over any field, agreement on the actual Abel morphism determines
both the actual group morphism and the equivariant regular torsor morphism. -/
theorem abelOneMap_equivariantPair_ext (φ ψ : groupScheme c D ⟶ H)
    (f g : picardOne c D ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f))
    (hg : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ g = (a ≫ ψ.hom.hom.hom) • (x ≫ g))
    (heq : abelOneMap c D ≫ f = abelOneMap c D ≫ g) : φ = ψ ∧ f = g := by
  let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ picardOne c D := ε ≫ abelOneMap c D
  let q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q := p ≫ f
  have hq : p ≫ g = q := by
    change (ε ≫ abelOneMap c D) ≫ g = (ε ≫ abelOneMap c D) ≫ f
    rw [Category.assoc, Category.assoc, heq]
  have hfm : f = picardOneEquivariantMap c D φ p q :=
    picardOneEquivariantMap_unique c D φ p q f rfl hf
  have hgm : g = picardOneEquivariantMap c D ψ p q :=
    picardOneEquivariantMap_unique c D ψ p q g hq hg
  have hm : abelOneMap c D ≫ picardOneEquivariantMap c D φ p q =
      abelOneMap c D ≫ picardOneEquivariantMap c D ψ p q :=
    (congrArg (fun a => abelOneMap c D ≫ a) hfm).symm.trans
      (heq.trans (congrArg (fun a => abelOneMap c D ≫ a) hgm))
  have hn : modulusAbelMap c D ε ≫ φ.hom.hom.hom =
      modulusAbelMap c D ε ≫ ψ.hom.hom.hom :=
    (abelOneMap_equivariantMap_coordinate c D ε φ q).symm.trans
      ((congrArg (fun a => a ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) q) hm).trans
        (abelOneMap_equivariantMap_coordinate c D ε ψ q))
  have hφ : φ = ψ := modulusAbel_groupHom_ext c D ε H φ ψ hn
  refine ⟨hφ, ?_⟩
  exact hfm.trans ((congrArg (fun a => picardOneEquivariantMap c D a p q) hφ).trans hgm.symm)


/-- Agreement on the intrinsic Abel map determines the group/map pair
without a rational point of the curve or the target torsor. A complement
point over the algebraic closure proves uniqueness there, and faithful
scalar extension reflects both equalities over the original field. -/
theorem abelOneMap_equivariantPair_ext_unpointed (φ ψ : groupScheme c D ⟶ H)
    (f g : picardOne c D ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f))
    (hg : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ g = (a ≫ ψ.hom.hom.hom) • (x ≫ g))
    (heq : abelOneMap c D ≫ f = abelOneMap c D ≫ g) : φ = ψ ∧ f = g := by
  let L := AlgebraicClosure K
  let F := Over.pullback (AlgebraicGeometry.SmoothProperCurve.specMap K L)
  let B := F.mapCommGrp
  let cL := AlgebraicGeometry.SmoothProperCurve.baseChange K c L
  let DL := D.changeBaseOfIdentity (AlgebraicGeometry.SmoothProperCurve.specMap K L)
  let sourceGroup := groupScheme cL DL
  let HL := B.obj H
  let QL := F.obj Q
  let eG : F.mapCommGrp.obj (groupScheme c D) ≅ groupScheme cL DL :=
    groupActualScalarExtensionIso c D L
  let eP : F.obj (picardOne c D) ≅ picardOne cL DL :=
    picardOneScalarExtensionIso c D L
  let _ : ModObj HL.X QL := F.modObjObj H.X Q
  have : IsIso (ModObj.leftSMul HL.X QL) := F.isIso_leftSMul_modObjObj H.X Q
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  let φL : sourceGroup ⟶ HL := eG.inv ≫ B.map φ
  let ψL : sourceGroup ⟶ HL := eG.inv ≫ B.map ψ
  let fL : picardOne cL DL ⟶ QL := eP.inv ≫ F.map f
  let gL : picardOne cL DL ⟶ QL := eP.inv ≫ F.map g
  have hfL : ∀ (T : Over (Spec (CommRingCat.of L))) (a : T ⟶ sourceGroup.X)
      (x : T ⟶ picardOne cL DL),
      (a • x) ≫ fL = (a ≫ φL.hom.hom.hom) • (x ≫ fL) :=
    picardOneMap_scalarExtension_equivariant c D L φ f hf
  have hgL : ∀ (T : Over (Spec (CommRingCat.of L))) (a : T ⟶ sourceGroup.X)
      (x : T ⟶ picardOne cL DL),
      (a • x) ≫ gL = (a ≫ ψL.hom.hom.hom) • (x ≫ gL) :=
    picardOneMap_scalarExtension_equivariant c D L ψ g hg
  have ha : abelOneMap cL DL ≫ eP.inv =
      modulusMapScalarExtension c D L (picardOne c D) (abelOneMap c D) := by
    apply (cancel_mono eP.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [modulusMapScalarExtension, Category.id_comp, cL, DL, eP] using
      (abelOneMap_scalarExtension c D L (𝟙 _)).symm
  have habel : abelOneMap cL DL ≫ fL = abelOneMap cL DL ≫ gL := by
    change abelOneMap cL DL ≫ (eP.inv ≫ F.map f) =
      abelOneMap cL DL ≫ (eP.inv ≫ F.map g)
    rw [← Category.assoc, ← Category.assoc, ha]
    rw [← modulusMapScalarExtension_comp, ← modulusMapScalarExtension_comp, heq]
  obtain ⟨εL⟩ := modulusComplement_point cL DL
  obtain ⟨hφ, hfg⟩ :=
    abelOneMap_equivariantPair_ext cL DL εL φL ψL fL gL hfL hgL habel
  have hflat : Flat (AlgebraicGeometry.SmoothProperCurve.specMap K L) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsurj : Surjective (AlgebraicGeometry.SmoothProperCurve.specMap K L) :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  have : F.Faithful := inferInstanceAs
    ((Over.pullback (AlgebraicGeometry.SmoothProperCurve.specMap K L)).Faithful)
  refine ⟨?_, ?_⟩
  · have hb : B.map φ = B.map ψ := (cancel_epi eG.inv).mp hφ
    apply CommGrp.hom_ext
    apply F.map_injective
    exact congrArg (fun a => a.hom.hom.hom) hb
  · apply F.map_injective
    exact (cancel_epi eP.inv).mp hfg

/-- Extending an equivariant Abel factor agrees with any factor of the
extended curve map, in every modulus degree and without a rational basepoint.
Both group and torsor comparisons are the canonical full-modulus isomorphisms. -/
theorem abelOneMap_equivariantPair_scalarExtension
    (L : Type u) [Field L] [Algebra K L]
    (φ : groupScheme c D ⟶ H) (f : picardOne c D ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f)) :
    let F := Over.pullback (SmoothProperCurve.specMap K L)
    let B := F.mapCommGrp
    let cL := SmoothProperCurve.baseChange K c L
    let DL := D.changeBaseOfIdentity (SmoothProperCurve.specMap K L)
    let _ : ModObj (B.obj H).X (F.obj Q) := F.modObjObj H.X Q
    ∀ (ψ : groupScheme cL DL ⟶ B.obj H) (g : picardOne cL DL ⟶ F.obj Q),
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ g = (a ≫ ψ.hom.hom.hom) • (x ≫ g)) →
      abelOneMap cL DL ≫ g =
        modulusMapScalarExtension c D L Q (abelOneMap c D ≫ f) →
      ψ = (groupActualScalarExtensionIso c D L).inv ≫ B.map φ ∧
        g = (picardOneScalarExtensionIso c D L).inv ≫ F.map f := by
  intro F B cL DL targetAction ψ g hg habel
  have : IsIso (ModObj.leftSMul (B.obj H).X (F.obj Q)) :=
    F.isIso_leftSMul_modObjObj H.X Q
  have : IsSeparated (B.obj H).X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  let eP : F.obj (picardOne c D) ≅ picardOne cL DL :=
    picardOneScalarExtensionIso c D L
  apply abelOneMap_equivariantPair_ext_unpointed cL DL ψ
    ((groupActualScalarExtensionIso c D L).inv ≫ B.map φ)
    g (eP.inv ≫ F.map f) hg
    (picardOneMap_scalarExtension_equivariant c D L φ f hf)
  have ha : abelOneMap cL DL ≫ eP.inv =
      modulusMapScalarExtension c D L (picardOne c D) (abelOneMap c D) := by
    apply (cancel_mono eP.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [modulusMapScalarExtension, Category.id_comp, cL, DL, eP] using
      (abelOneMap_scalarExtension c D L (𝟙 _)).symm
  rw [habel, ← Category.assoc, ha, modulusMapScalarExtension_comp]

/-- Compatibility with an arbitrary pullback comparison reduces tower uniqueness
to the known action and Abel squares. -/
private theorem abelOneMap_equivariantPair_tower_core
    (L : Type u) [Field L] [Algebra K L]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let HL := FKL.mapCommGrp.obj H
    let HM := FKM.mapCommGrp.obj H
    let _ : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _ : ModObj HM.X (FKM.obj Q) := FKM.modObjObj H.X Q
      ∀ (e : FKM ≅ FKL ⋙ FLM),
      let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    ∀ (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ FKL.obj Q)
      (φM : groupScheme cM DM ⟶ HM) (fM : picardOne cM DM ⟶ FKM.obj Q),
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ fL = (a ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      abelOneMap cM DM ≫ fM = modulusMapScalarExtension c D M Q q →
      (∀ (T : Over (Spec (CommRingCat.of M)))
        (a : T ⟶ (groupScheme cM DM).X) (x : T ⟶ picardOne cM DM),
          (a • x) ≫ fM = (a ≫ φM.hom.hom.hom) • (x ≫ fM)) →
      FLM.mapCommGrp.map
          ((groupActualScalarExtensionIso c D L).hom ≫ φL) =
        (eB.app (groupScheme c D)).inv ≫
          ((groupActualScalarExtensionIso c D M).hom ≫ φM) ≫ (eB.app H).hom ∧
      FLM.map ((picardOneScalarExtensionIso c D L).hom ≫ fL) =
        e.inv.app (picardOne c D) ≫
          ((picardOneScalarExtensionIso c D M).hom ≫ fM) ≫ e.hom.app Q := by
  intro FKL FLM FKM cL DL cM DM HL HM actionL actionM e eB
    φL fL φM fM hAbelL hfL hAbelM hfM
  let gL : FKL.mapCommGrp.obj (groupScheme c D) ≅ groupScheme cL DL :=
    groupActualScalarExtensionIso c D L
  let gM : FKM.mapCommGrp.obj (groupScheme c D) ≅ groupScheme cM DM :=
    groupActualScalarExtensionIso c D M
  let gLM : FLM.mapCommGrp.obj (groupScheme cL DL) ≅
      groupScheme (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M)) :=
    groupActualScalarExtensionIso cL DL M
  let cLM := baseChange L cL M
  let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
  let eG : groupScheme cLM DLM ≅ groupScheme cM DM := gLM.symm ≪≫
    FLM.mapCommGrp.mapIso gL.symm ≪≫
      (eB.app (groupScheme c D)).symm ≪≫ gM
  let aL : FKL.obj (picardOne c D) ≅ picardOne cL DL :=
    picardOneScalarExtensionIso c D L
  let aM : FKM.obj (picardOne c D) ≅ picardOne cM DM :=
    picardOneScalarExtensionIso c D M
  let aLM : FLM.obj (picardOne cL DL) ≅ picardOne cLM DLM :=
    picardOneScalarExtensionIso cL DL M
  let eP : picardOne cLM DLM ≅ picardOne cM DM :=
    aLM.symm ≪≫ FLM.mapIso aL.symm ≪≫ (e.app (picardOne c D)).symm ≪≫ aM
  let HLM : CommGrp (Over (Spec (CommRingCat.of M))) := FLM.mapCommGrp.obj HL
  let _ : ModObj HLM.X (FLM.obj (FKL.obj Q)) := FLM.modObjObj HL.X (FKL.obj Q)
  let _ : ModObj (groupScheme cLM DLM).X (picardOne cLM DLM) :=
    picardOneModObj cLM (DL.changeBaseOfIdentity (f := cL) (specMap L M))
  let t : HM ⟶ HLM := comp_obj_hom FKL.mapCommGrp FLM.mapCommGrp (eB.app H).hom
  let p : FKM.obj Q ⟶ FLM.obj (FKL.obj Q) := comp_obj_hom FKL FLM (e.hom.app Q)
  let ψ : groupScheme cLM DLM ⟶ HLM := eG.hom ≫ φM ≫ t
  let f : picardOne cLM DLM ⟶ FLM.obj (FKL.obj Q) := eP.hom ≫ fM ≫ p
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  have : IsIso (ModObj.leftSMul HL.X (FKL.obj Q)) := FKL.isIso_leftSMul_modObjObj H.X Q
  have ht : ∀ (T : Over (Spec (CommRingCat.of M)))
      (a : T ⟶ HM.X) (x : T ⟶ FKM.obj Q),
      (a • x) ≫ p = (a ≫ t.hom.hom.hom) • (x ≫ p) :=
    pullback_tower_action (specMap K L) (specMap L M) (specMap K M) e H Q
      actionM rfl (FLM.modObjObj HL.X (FKL.obj Q)) rfl t rfl p rfl
  have hf : ∀ (T : Over (Spec (CommRingCat.of M)))
      (a : T ⟶ (groupScheme cLM DLM).X) (x : T ⟶ picardOne cLM DLM),
      (a • x) ≫ f = (a ≫ ψ.hom.hom.hom) • (x ≫ f) :=
    equivariant_commGrp_tower_comp_apply FKM FKL FLM e
      (groupScheme c D) (picardOne c D)
      (groupScheme cL DL) (picardOne cL DL)
      (groupScheme cLM DLM) (groupScheme cM DM) HM HLM
      (picardOne cLM DLM) (picardOne cM DM) (FKM.obj Q) (FLM.obj (FKL.obj Q))
      gL.symm aL.symm gLM.symm aLM.symm gM aM
      φM t fM p hfM ht
      (fun _ a x => picardOneScalarExtensionIso_inv_smul c D L a x)
      (fun _ a x => picardOneScalarExtensionIso_inv_smul cL DL M a x)
      (fun _ a x => picardOneScalarExtensionIso_smul c D M a x)
  have hfac : abelOneMap cLM DLM ≫ f =
      modulusMapScalarExtension cL DL M (FKL.obj Q) (abelOneMap cL DL ≫ fL) := by
    exact (abelOneMap_scalarExtension_tower_factorization c D L M Q q e fM hAbelM).trans
      (congrArg (modulusMapScalarExtension cL DL M (FKL.obj Q)) hAbelL).symm
  have hpair :=
    abelOneMap_equivariantPair_scalarExtension cL DL M φL fL hfL ψ f hf hfac
  refine ⟨?_, ?_⟩
  · exact map_eq_of_iso_transport FLM.mapCommGrp gL gLM
      (eB.app (groupScheme c D)).symm gM φM (eB.app H).hom φL hpair.1
  · exact map_eq_of_iso_transport FLM aL aLM
      (e.app (picardOne c D)).symm aM fM (e.hom.app Q) fL hpair.2


/-- A factor constructed over an intermediate field and one constructed over
the final field give the same pair after the actual pullback tower comparisons.
Neither factor needs a rational basepoint. This compares the two ways used on
geometric fibres of the descent overlap; it does not assume their equality. -/
theorem abelOneMap_equivariantPair_tower
    (L : Type u) [Field L] [Algebra K L]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let HL := FKL.mapCommGrp.obj H
    let HM := FKM.mapCommGrp.obj H
    let _ : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _ : ModObj HM.X (FKM.obj Q) := FKM.modObjObj H.X Q
    ∀ (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ FKL.obj Q)
      (φM : groupScheme cM DM ⟶ HM) (fM : picardOne cM DM ⟶ FKM.obj Q),
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ fL = (a ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      abelOneMap cM DM ≫ fM = modulusMapScalarExtension c D M Q q →
      (∀ (T : Over (Spec (CommRingCat.of M)))
        (a : T ⟶ (groupScheme cM DM).X) (x : T ⟶ picardOne cM DM),
          (a • x) ≫ fM = (a ≫ φM.hom.hom.hom) • (x ≫ fM)) →
      let w : specMap L M ≫ specMap K L = specMap K M := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]
      let e : FKM ≅ FKL ⋙ FLM :=
        (eqToIso (congrArg
          (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
            Over.pullbackComp (specMap L M) (specMap K L)
      let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
      FLM.mapCommGrp.map
          ((groupActualScalarExtensionIso c D L).hom ≫ φL) =
        (eB.app (groupScheme c D)).inv ≫
          ((groupActualScalarExtensionIso c D M).hom ≫ φM) ≫ (eB.app H).hom ∧
      FLM.map ((picardOneScalarExtensionIso c D L).hom ≫ fL) =
        e.inv.app (picardOne c D) ≫
          ((picardOneScalarExtensionIso c D M).hom ≫ fM) ≫ e.hom.app Q := by
  intro FKL FLM FKM cL DL cM DM HL HM actionL actionM
  let w : specMap L M ≫ specMap K L = specMap K M := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]
  let e : FKM ≅ FKL ⋙ FLM :=
    (eqToIso (congrArg
      (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
        Over.pullbackComp (specMap L M) (specMap K L)
  exact abelOneMap_equivariantPair_tower_core c D (H := H) (Q := Q) L M q e

/-- A torsor factor has the same geometric value as a factor over the
final field whenever the two source points project to the same original
Picard-one point. The point itself supplies the intermediate field action;
no choice of an embedding of the intermediate field is fixed in advance. -/
theorem abelOneMap_equivariantPair_torsor_value
    (L : Type u) [Field L] [Algebra K L]
    (M : Type u) [Field M] [Algebra K M]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let FKL := Over.pullback (specMap K L)
    let FKM := Over.pullback (specMap K M)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let HL := FKL.mapCommGrp.obj H
    let HM := FKM.mapCommGrp.obj H
    let _ : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _ : ModObj HM.X (FKM.obj Q) := FKM.modObjObj H.X Q
    ∀ (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ FKL.obj Q)
      (φM : groupScheme cM DM ⟶ HM) (fM : picardOne cM DM ⟶ FKM.obj Q),
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ fL = (a ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      abelOneMap cM DM ≫ fM = modulusMapScalarExtension c D M Q q →
      (∀ (T : Over (Spec (CommRingCat.of M)))
        (a : T ⟶ (groupScheme cM DM).X) (x : T ⟶ picardOne cM DM),
          (a • x) ≫ fM = (a ≫ φM.hom.hom.hom) • (x ≫ fM)) →
      ∀ (x : Spec (CommRingCat.of M) ⟶
          Limits.pullback (picardOne c D).hom (specMap K L))
        (y : Spec (CommRingCat.of M) ⟶
          Limits.pullback (picardOne c D).hom (specMap K M)),
        y ≫ Limits.pullback.snd (picardOne c D).hom (specMap K M) = 𝟙 _ →
        x ≫ Limits.pullback.fst (picardOne c D).hom (specMap K L) =
          y ≫ Limits.pullback.fst (picardOne c D).hom (specMap K M) →
        x ≫ ((picardOneScalarExtensionIso c D L).hom ≫ fL).left ≫
            Limits.pullback.fst Q.hom (specMap K L) =
          y ≫ ((picardOneScalarExtensionIso c D M).hom ≫ fM).left ≫
            Limits.pullback.fst Q.hom (specMap K M) := by
  intro FKL FKM cL DL cM DM HL HM actionL actionM
    φL fL φM fM hAbelL hfL hAbelM hfM x y hy hxy
  apply overPullback_specMap_field_map_value (K := K) (L := L) (M := M)
    (X := picardOne c D) (Y := Q)
    ((picardOneScalarExtensionIso c D L).hom ≫ fL)
    ((picardOneScalarExtensionIso c D M).hom ≫ fM) ?_ x y hy hxy
  intro algebraLM tower sKL sLM sKM w e
  have hpair :=
    abelOneMap_equivariantPair_tower_core c D L M q e φL fL φM fM hAbelL hfL hAbelM hfM
  exact hpair.2


/-- The group component of an equivariant Abel factor has the same geometric
value along any embedding determined by the source point. It uses the same
tower comparison and field-action construction as the torsor component. -/
theorem abelOneMap_equivariantPair_group_value
    (L : Type u) [Field L] [Algebra K L]
    (M : Type u) [Field M] [Algebra K M]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let FKL := Over.pullback (specMap K L)
    let FKM := Over.pullback (specMap K M)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let HL := FKL.mapCommGrp.obj H
    let HM := FKM.mapCommGrp.obj H
    let _ : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _ : ModObj HM.X (FKM.obj Q) := FKM.modObjObj H.X Q
    ∀ (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ FKL.obj Q)
      (φM : groupScheme cM DM ⟶ HM) (fM : picardOne cM DM ⟶ FKM.obj Q),
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ fL = (a ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      abelOneMap cM DM ≫ fM = modulusMapScalarExtension c D M Q q →
      (∀ (T : Over (Spec (CommRingCat.of M)))
        (a : T ⟶ (groupScheme cM DM).X) (x : T ⟶ picardOne cM DM),
          (a • x) ≫ fM = (a ≫ φM.hom.hom.hom) • (x ≫ fM)) →
      let mL : FKL.obj (groupScheme c D).X ⟶ FKL.obj H.X :=
        groupActualScalarExtensionMap c D L ≫ φL.hom.hom.hom
      let mM : FKM.obj (groupScheme c D).X ⟶ FKM.obj H.X :=
        groupActualScalarExtensionMap c D M ≫ φM.hom.hom.hom
      ∀ (x : Spec (CommRingCat.of M) ⟶
          Limits.pullback (groupScheme c D).X.hom (specMap K L))
        (y : Spec (CommRingCat.of M) ⟶
          Limits.pullback (groupScheme c D).X.hom (specMap K M)),
        y ≫ Limits.pullback.snd (groupScheme c D).X.hom (specMap K M) = 𝟙 _ →
        x ≫ Limits.pullback.fst (groupScheme c D).X.hom (specMap K L) =
          y ≫ Limits.pullback.fst (groupScheme c D).X.hom (specMap K M) →
        x ≫ mL.left ≫ Limits.pullback.fst H.X.hom (specMap K L) =
          y ≫ mM.left ≫ Limits.pullback.fst H.X.hom (specMap K M) := by
  intro FKL FKM cL DL cM DM HL HM actionL actionM
    φL fL φM fM hAbelL hfL hAbelM hfM mL mM x y hy hxy
  let bL : FKL.mapCommGrp.obj (groupScheme c D) ⟶ HL :=
    (groupActualScalarExtensionIso c D L).hom ≫ φL
  let bM : FKM.mapCommGrp.obj (groupScheme c D) ⟶ HM :=
    (groupActualScalarExtensionIso c D M).hom ≫ φM
  have h := commGrp_specMap_field_map_value (K := K) (L := L) (M := M)
    (G := groupScheme c D) (H := H) bL bM (by
      intro algebraLM tower sKL sLM sKM w e eB
      exact (abelOneMap_equivariantPair_tower_core c D (H := H) (Q := Q)
        L M q e φL fL φM fM hAbelL hfL hAbelM hfM).1) x y hy hxy
  have hL : mapCommGrp_underlying FKL bL = mL :=
    groupActualScalarExtensionMap_comp c D L φL
  have hM : mapCommGrp_underlying FKM bM = mM :=
    groupActualScalarExtensionMap_comp c D M φM
  exact (congrArg
    (fun m : FKL.obj (groupScheme c D).X ⟶ FKL.obj H.X =>
      x ≫ m.left ≫ Limits.pullback.fst H.X.hom (specMap K L)) hL).symm.trans
    (h.trans (congrArg
      (fun m : FKM.obj (groupScheme c D).X ⟶ FKM.obj H.X =>
        y ≫ m.left ≫ Limits.pullback.fst H.X.hom (specMap K M)) hM))

/-- A concrete group factor of the coordinate map constructs the unique
regular equivariant pair. This is the common torsor construction used after
the modulus condition has supplied the group factor. -/
theorem picardOneEquivariantMap_factors_uniquely
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (φ : groupScheme c D ⟶ H)
    (hφ : modulusAbelMap c D ε ≫ φ.hom.hom.hom =
      q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε ≫ q)) :
    ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  let f : picardOne c D ⟶ Q :=
    picardOneEquivariantMap c D φ (ε ≫ abelOneMap c D) (ε ≫ q)
  have hf : abelOneMap c D ≫ f = q := by
    apply (cancel_mono
      (SchemeTheory.PointedTorsor.trivialization (G := H.X) (ε ≫ q)).hom).mp
    exact (abelOneMap_equivariantMap_coordinate c D ε φ (ε ≫ q)).trans hφ
  have heq : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
      (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f) :=
    fun _ a x => picardOneEquivariantMap_equivariant c D φ
      (ε ≫ abelOneMap c D) (ε ≫ q) a x
  refine ⟨(φ, f), ⟨hf, heq⟩, ?_⟩
  intro fg hfg
  obtain ⟨hgroup, htorsor⟩ := abelOneMap_equivariantPair_ext c D ε
    fg.1 φ fg.2 f hfg.2 heq (hfg.1.trans hf.symm)
  exact Prod.ext hgroup htorsor


/-- Equivariant Abel factors for nested full moduli commute with both actual
transitions. This applies in every degree once the two factors are supplied. -/
theorem abelOneMap_equivariantPair_restrict
    {e : ℕ} (E : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of K))))
    (hED : E.I ≤ D.I)
    (φ : groupScheme c D ⟶ H) (ψ : groupScheme c E ⟶ H)
    (f : picardOne c D ⟶ Q) (g : picardOne c E ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f))
    (hg : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c E).X) (x : T ⟶ picardOne c E),
        (a • x) ≫ g = (a ≫ ψ.hom.hom.hom) • (x ≫ g))
    (habel : abelOneMap c E ≫ g =
      modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hED)
        (modulusIdealInclusion_curve c E D hED) ≫ abelOneMap c D ≫ f) :
    ψ = transition c E D hED ≫ φ ∧
      g = picardOneTransition c E D hED ≫ f := by
  apply abelOneMap_equivariantPair_ext_unpointed c E
    ψ (transition c E D hED ≫ φ) g (picardOneTransition c E D hED ≫ f) hg
  · intro T a x
    have ht :
        (a • x) ≫ picardOneTransition c E D hED =
          (a ≫ (transition c E D hED).hom.hom.hom) •
            (x ≫ picardOneTransition c E D hED) :=
      picardOneTransitionAlong_smul c E D (Scheme.IdealSheafData.inclusion hED)
        (modulusIdealInclusion_curve c E D hED) a x
    calc
      (a • x) ≫ (picardOneTransition c E D hED ≫ f) =
          ((a • x) ≫ picardOneTransition c E D hED) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = ((a ≫ (transition c E D hED).hom.hom.hom) •
          (x ≫ picardOneTransition c E D hED)) ≫ f := by rw [ht]
      _ = ((a ≫ (transition c E D hED).hom.hom.hom) ≫ φ.hom.hom.hom) •
          ((x ≫ picardOneTransition c E D hED) ≫ f) := hf T _ _
      _ = (a ≫ (transition c E D hED ≫ φ).hom.hom.hom) •
          (x ≫ (picardOneTransition c E D hED ≫ f)) := by
        change ((a ≫ (transition c E D hED).hom.hom.hom) ≫ φ.hom.hom.hom) •
          ((x ≫ picardOneTransition c E D hED) ≫ f) =
            (a ≫ ((transition c E D hED).hom.hom.hom ≫ φ.hom.hom.hom)) •
              (x ≫ (picardOneTransition c E D hED ≫ f))
        simp only [Category.assoc]
  · rw [← Category.assoc, abelOneMap_transition, Category.assoc]
    exact habel

omit [IsIso (ModObj.leftSMul H.X Q)] [IsSeparated H.X.hom] in
/-- Postcomposition by an actual equivariant target map commutes with both
components of an Abel factorization, in every modulus degree. -/
theorem abelOneMap_equivariantPair_comp
    (H' : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H'.X.hom]
    (Q' : Over (Spec (CommRingCat.of K))) [ModObj H'.X Q']
    [IsIso (ModObj.leftSMul H'.X Q')]
    (ρ : H ⟶ H') (r : Q ⟶ Q')
    (hr : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ H.X) (x : T ⟶ Q),
        (a • x) ≫ r = (a ≫ ρ.hom.hom.hom) • (x ≫ r))
    (φ : groupScheme c D ⟶ H) (ψ : groupScheme c D ⟶ H')
    (f : picardOne c D ⟶ Q) (g : picardOne c D ⟶ Q')
    (hf : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ f = (a ≫ φ.hom.hom.hom) • (x ≫ f))
    (hg : ∀ (T : Over (Spec (CommRingCat.of K)))
      (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
        (a • x) ≫ g = (a ≫ ψ.hom.hom.hom) • (x ≫ g))
    (habel : abelOneMap c D ≫ g = (abelOneMap c D ≫ f) ≫ r) :
    ψ = φ ≫ ρ ∧ g = f ≫ r := by
  apply abelOneMap_equivariantPair_ext_unpointed c D ψ (φ ≫ ρ) g (f ≫ r) hg
  · intro T a x
    calc
      (a • x) ≫ (f ≫ r) = ((a • x) ≫ f) ≫ r := (Category.assoc _ _ _).symm
      _ = ((a ≫ φ.hom.hom.hom) • (x ≫ f)) ≫ r := by rw [hf]
      _ = ((a ≫ φ.hom.hom.hom) ≫ ρ.hom.hom.hom) • ((x ≫ f) ≫ r) := hr T _ _
      _ = (a ≫ (φ ≫ ρ).hom.hom.hom) • (x ≫ (f ≫ r)) := by
        change ((a ≫ φ.hom.hom.hom) ≫ ρ.hom.hom.hom) • ((x ≫ f) ≫ r) =
          (a ≫ (φ.hom.hom.hom ≫ ρ.hom.hom.hom)) • (x ≫ (f ≫ r))
        simp only [Category.assoc]
  · exact habel.trans (Category.assoc _ _ _)

end AlgebraicGeometry.GeneralizedJacobian
