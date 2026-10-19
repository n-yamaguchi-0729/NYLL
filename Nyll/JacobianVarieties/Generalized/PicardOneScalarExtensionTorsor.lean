/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionAction
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionScheme
import Nyll.JacobianVarieties.Generalized.PicardOneSchemeAction
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupScheme
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupSchemeMap
import Nyll.JacobianVarieties.Generalized.PicardOneModuleObject
import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparison
import Nyll.SchemeTheory.CategoryTheory.EquivariantScalarTowerComparison
import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorMap
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-! # Scalar extension of the actual degree-one scheme action -/

noncomputable section

universe u v u' v'

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- The action obtained by adjoint transpose is the monoidal transport of
that same action. The calculation is performed before concrete group schemes
and their represented group laws are substituted. -/
private theorem adjunction_transportAction
    {A : Type u} [Category.{v} A] [CartesianMonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [CartesianMonoidalCategory B]
    {F : A ⥤ B} {G : B ⥤ A} [G.Monoidal]
    (adj : F ⊣ G) (M P : B) [MonObj M] [ModObj M P] :
    adj.homEquiv (G.obj M ⊗ G.obj P) P
        (lift ((adj.homEquiv (G.obj M ⊗ G.obj P) M).symm
            (fst (G.obj M) (G.obj P)))
          ((adj.homEquiv (G.obj M ⊗ G.obj P) P).symm
            (snd (G.obj M) (G.obj P))) ≫ γ[M, P]) =
      Functor.LaxMonoidal.μ G M P ≫ G.map γ[M, P] := by
  let _ : ModObj (G.obj M) (G.obj P) := G.modObjObj M P
  change adj.homEquiv (G.obj M ⊗ G.obj P) P
      (((adj.homEquiv (G.obj M ⊗ G.obj P) M).symm
          (fst (G.obj M) (G.obj P))) •
        ((adj.homEquiv (G.obj M ⊗ G.obj P) P).symm
          (snd (G.obj M) (G.obj P)))) = γ[G.obj M, G.obj P]
  rw [adj.homEquiv_modObj_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change lift (fst (G.obj M) (G.obj P)) (snd (G.obj M) (G.obj P)) ≫
    γ[G.obj M, G.obj P] = γ[G.obj M, G.obj P]
  rw [lift_fst_snd, Category.id_comp]

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The pullback of the actual tensor action, defined by the universal property of base change. -/
def picardOneScalarExtensionAction :
    (groupScalarExtension c D L).X ⊗ (Over.pullback (specMap K L)).obj (picardOne c D) ⟶
      (Over.pullback (specMap K L)).obj (picardOne c D) :=
  (Over.mapPullbackAdj (specMap K L)).homEquiv _ _
    (lift (((Over.mapPullbackAdj (specMap K L)).homEquiv _ _).symm (fst _ _))
      (((Over.mapPullbackAdj (specMap K L)).homEquiv _ _).symm (snd _ _)) ≫
        picardOneTensorAction c D)

/-- The pulled-back action still classifies the actual original tensor product on every test. -/
theorem picardOneScalarExtensionAction_classifies {T : Over (Spec (CommRingCat.of L))}
    (g : T ⟶ (groupScalarExtension c D L).X)
    (x : T ⟶ (Over.pullback (specMap K L)).obj (picardOne c D)) :
    (picardOneScalarExtensionRepresentable c D L).homEquiv
        (lift g x ≫ picardOneScalarExtensionAction c D L) =
      modulusPicardOneIntrinsicAction c (modulusCurveMap D) ((Over.map (specMap K L)).obj T)
        ((groupScalarExtensionRepresentable c D L).homEquiv g)
        ((picardOneScalarExtensionRepresentable c D L).homEquiv x) := by
  let A := Over.mapPullbackAdj (specMap K L)
  let F := Over.map (specMap K L)
  let G := (groupScalarExtension c D L).X
  let P := (Over.pullback (specMap K L)).obj (picardOne c D)
  let g₀ := (A.homEquiv (G ⊗ P) (groupScheme c D).X).symm (fst G P)
  let x₀ := (A.homEquiv (G ⊗ P) (picardOne c D)).symm (snd G P)
  change (picardOneRepresentable c D).homEquiv
    ((A.homEquiv T (picardOne c D)).symm
      (lift g x ≫ A.homEquiv (G ⊗ P) (picardOne c D)
        (lift g₀ x₀ ≫ picardOneTensorAction c D))) = _
  rw [A.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, ← Category.assoc, comp_lift]
  have hg : F.map (lift g x) ≫ g₀ =
      (A.homEquiv T (groupScheme c D).X).symm g :=
    (A.homEquiv_naturality_left_symm (lift g x) (fst G P)).symm.trans
      (congrArg (A.homEquiv T (groupScheme c D).X).symm (lift_fst g x))
  have hx : F.map (lift g x) ≫ x₀ = (A.homEquiv T (picardOne c D)).symm x :=
    (A.homEquiv_naturality_left_symm (lift g x) (snd G P)).symm.trans
      (congrArg (A.homEquiv T (picardOne c D)).symm (lift_snd g x))
  rw [hg, hx]
  exact picardOneTensorAction_classifies c D _ _

/-- The scalar-extension scheme comparisons intertwine the actual two tensor actions. -/
theorem picardOneScalarExtensionIso_action {T : Over (Spec (CommRingCat.of L))}
    (g : T ⟶ (groupScalarExtension c D L).X)
    (x : T ⟶ (Over.pullback (specMap K L)).obj (picardOne c D)) :
    (lift g x ≫ picardOneScalarExtensionAction c D L) ≫
        (picardOneScalarExtensionIso c D L).hom =
      lift (g ≫ (groupScalarExtensionIso c D L).hom.hom.hom.hom)
        (x ≫ (picardOneScalarExtensionIso c D L).hom) ≫
          picardOneTensorAction (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) := by
  let c' := baseChange K c L
  let D' := D.changeBaseOfIdentity (specMap K L)
  let a := modulusPicardOneSheaf_divisorScalarExtensionIso D L
  let b := modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L
  let E := (((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
    (Type (u + 1))).mapIso a).app (op T)).toEquiv
  apply (picardOneRepresentable c' D').homEquiv.injective
  apply E.injective
  change a.hom.hom.app (op T) _ = a.hom.hom.app (op T) _
  rw [picardOneScalarExtensionIso_homEquiv, picardOneScalarExtensionAction_classifies,
    picardOneTensorAction_classifies]
  have ha : a.hom.hom.app (op T) (a.inv.hom.app (op T)
      ((picardOneScalarExtensionRepresentable c D L).homEquiv x)) =
        (picardOneScalarExtensionRepresentable c D L).homEquiv x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun q => q.hom) a.inv_hom_id) (op T)) _
  have hb : (b.hom.hom.app (op T)).hom ((b.inv.hom.app (op T)).hom
      ((groupScalarExtensionRepresentable c D L).homEquiv g)) =
        (groupScalarExtensionRepresentable c D L).homEquiv g :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun q => q.hom) b.inv_hom_id) (op T)) _
  have ht := modulusPicardOneSheaf_divisorScalarExtension_action D L T
    ((b.inv.hom.app (op T)).hom ((groupScalarExtensionRepresentable c D L).homEquiv g))
    (a.inv.hom.app (op T) ((picardOneScalarExtensionRepresentable c D L).homEquiv x))
  rw [groupScalarExtensionIso_homEquiv, picardOneScalarExtensionIso_homEquiv]
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun q => q.hom) a.inv_hom_id) (op T)) _).trans
      ((congrArg₂ (modulusPicardOneIntrinsicAction c (modulusCurveMap D)
        ((Over.map (specMap K L)).obj T)) hb ha).symm.trans ht.symm)


/-- The previously represented scalar-extension action is the action
transported by the native monoidal pullback functor. -/
theorem picardOneScalarExtensionAction_eq :
    picardOneScalarExtensionAction c D L =
      Functor.LaxMonoidal.μ (Over.pullback (specMap K L))
          (groupScheme c D).X (picardOne c D) ≫
        (Over.pullback (specMap K L)).map (picardOneTensorAction c D) := by
  exact adjunction_transportAction (Over.mapPullbackAdj (specMap K L))
    (groupScheme c D).X (picardOne c D)

/-- The native group and Picard-one comparisons intertwine the same
transported module-object action, on every parameter scheme. -/
theorem picardOneScalarExtensionIso_smul {T : Over (Spec (CommRingCat.of L))}
    (g : T ⟶ ((GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D)).X)
    (x : T ⟶ (Over.pullback (specMap K L)).obj (picardOne c D)) :
    let _ : ModObj (((GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D)).X)
        ((Over.pullback (specMap K L)).obj (picardOne c D)) :=
      (Over.pullback (specMap K L)).modObjObj (groupScheme c D).X (picardOne c D)
    (g • x) ≫ (picardOneScalarExtensionIso c D L).hom =
      (g ≫ (groupActualScalarExtensionIso c D L).hom.hom.hom.hom) •
        (x ≫ (picardOneScalarExtensionIso c D L).hom) := by
  intro transportedAction
  have ha := congrArg
    (fun f => (lift g x ≫ f) ≫ (picardOneScalarExtensionIso c D L).hom)
    (picardOneScalarExtensionAction_eq c D L)
  have hb := congrArg
    (fun f => lift (g ≫ f) (x ≫ (picardOneScalarExtensionIso c D L).hom) ≫
      picardOneTensorAction (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))
    (groupActualScalarExtensionIso_hom c D L)
  exact ha.symm.trans ((picardOneScalarExtensionIso_action c D L g x).trans hb.symm)



/-- The inverse comparisons preserve the same native actions. -/
theorem picardOneScalarExtensionIso_inv_smul {T : Over (Spec (CommRingCat.of L))}
    (g : T ⟶ (groupScheme (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L))).X)
    (x : T ⟶ picardOne (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))) :
    let _ : ModObj (((GroupSchemes.baseChange (specMap K L)).obj (groupScheme c D)).X)
        ((Over.pullback (specMap K L)).obj (picardOne c D)) :=
      (Over.pullback (specMap K L)).modObjObj (groupScheme c D).X (picardOne c D)
    (g • x) ≫ (picardOneScalarExtensionIso c D L).inv =
      (g ≫ (groupActualScalarExtensionIso c D L).inv.hom.hom.hom) •
        (x ≫ (picardOneScalarExtensionIso c D L).inv) := by
  intro transportedAction
  let e := groupActualScalarExtensionIso c D L
  have he : e.inv.hom.hom.hom ≫ e.hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun h => h.hom.hom.hom) e.inv_hom_id
  apply (cancel_mono (picardOneScalarExtensionIso c D L).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    picardOneScalarExtensionIso_smul, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  change g • x = (g ≫ (e.inv.hom.hom.hom ≫ e.hom.hom.hom.hom)) • x
  rw [he, Category.comp_id]


/-- The actual group comparison from the iterated scalar extension to the direct one.
Its construction is shared with the action comparison rather than reconstructed there. -/
def groupScalarExtensionTowerIso
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    groupScheme (baseChange L (baseChange K c L) M)
        ((D.changeBaseOfIdentity (specMap K L)).changeBaseOfIdentity
          (f := baseChange K c L) (specMap L M)) ≅
      groupScheme (baseChange K c M) (D.changeBaseOfIdentity (specMap K M)) :=
  scalarTowerComparisonIso (Over.pullback (specMap K M)).mapCommGrp
    (Over.pullback (specMap K L)).mapCommGrp (Over.pullback (specMap L M)).mapCommGrp
    (Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso)
    (groupActualScalarExtensionIso c D L).symm
    (groupActualScalarExtensionIso (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) M).symm
    (groupActualScalarExtensionIso c D M)

/-- The actual Picard-one comparison for an iterated scalar extension, using the same
object-level tower construction as its equivariant group comparison. -/
def picardOneScalarExtensionTowerIso
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    picardOne (baseChange L (baseChange K c L) M)
        ((D.changeBaseOfIdentity (specMap K L)).changeBaseOfIdentity
          (f := baseChange K c L) (specMap L M)) ≅
      picardOne (baseChange K c M) (D.changeBaseOfIdentity (specMap K M)) :=
  scalarTowerComparisonIso (Over.pullback (specMap K M))
    (Over.pullback (specMap K L)) (Over.pullback (specMap L M)) e
    (picardOneScalarExtensionIso c D L).symm
    (picardOneScalarExtensionIso (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) M).symm
    (picardOneScalarExtensionIso c D M)

/-- Equivariance of the actual tower comparisons holds for any natural
isomorphism between the direct and iterated pullback functors. -/
theorem picardOneScalarExtension_tower_smul_of_iso
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let G₀ := groupScheme c D
    let G₁ := groupScheme cL DL
    let G₂ := groupScheme (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let G₃ := groupScheme (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let P₀ := picardOne c D
    let P₁ := picardOne cL DL
    let P₂ := picardOne (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let P₃ := picardOne (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let _action₂ : ModObj G₂.X P₂ :=
      picardOneModObj (baseChange L cL M)
        (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let _action₃ : ModObj G₃.X P₃ :=
      picardOneModObj (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let aL : FKL.obj P₀ ≅ P₁ := picardOneScalarExtensionIso c D L
    let aM : FKM.obj P₀ ≅ P₃ := picardOneScalarExtensionIso c D M
    let aLM : FLM.obj P₁ ≅ P₂ := picardOneScalarExtensionIso cL DL M
    let bL : FKL.mapCommGrp.obj G₀ ≅ G₁ := groupActualScalarExtensionIso c D L
    let bM : FKM.mapCommGrp.obj G₀ ≅ G₃ := groupActualScalarExtensionIso c D M
    let bLM : FLM.mapCommGrp.obj G₁ ≅ G₂ := groupActualScalarExtensionIso cL DL M
    let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    let eG := bLM.symm ≪≫
      FLM.mapCommGrp.mapIso bL.symm ≪≫
        (eB.app G₀).symm ≪≫ bM
    let eP := aLM.symm ≪≫ FLM.mapIso aL.symm ≪≫
      (e.app P₀).symm ≪≫ aM
    ∀ (T : Over (Spec (CommRingCat.of M)))
      (g : T ⟶ G₂.X) (x : T ⟶ P₂),
      (g • x) ≫ eP.hom = (g ≫ eG.hom.hom.hom.hom) • (x ≫ eP.hom) := by
  intro cL DL FKL FLM FKM G₀ G₁ G₂ G₃ P₀ P₁ P₂ P₃ action₂
    action₃ aL aM aLM bL bM bLM eB eG eP T g x
  exact equivariant_commGrp_tower_apply FKM FKL FLM e
    G₀ P₀ G₁ P₁ G₂ G₃ P₂ P₃
    bL.symm aL.symm bLM.symm aLM.symm bM aM
    (fun _ a p => picardOneScalarExtensionIso_inv_smul c D L a p)
    (fun _ a p => picardOneScalarExtensionIso_inv_smul cL DL M a p)
    (fun _ a p => picardOneScalarExtensionIso_smul c D M a p) T g x

/-- The shared actual tower comparisons intertwine the two native Picard-one actions.
The proof applies the abstract tower calculation directly to the original three comparisons. -/
theorem picardOneScalarExtensionTowerIso_smul
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let G₀ := groupScheme c D
    let G₁ := groupScheme cL DL
    let G₂ := groupScheme (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let G₃ := groupScheme (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let P₀ := picardOne c D
    let P₁ := picardOne cL DL
    let P₂ := picardOne (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let P₃ := picardOne (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let _action₂ : ModObj G₂.X P₂ :=
      picardOneModObj (baseChange L cL M)
        (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let _action₃ : ModObj G₃.X P₃ :=
      picardOneModObj (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let aL : FKL.obj P₀ ≅ P₁ := picardOneScalarExtensionIso c D L
    let aM : FKM.obj P₀ ≅ P₃ := picardOneScalarExtensionIso c D M
    let aLM : FLM.obj P₁ ≅ P₂ := picardOneScalarExtensionIso cL DL M
    let bL : FKL.mapCommGrp.obj G₀ ≅ G₁ := groupActualScalarExtensionIso c D L
    let bM : FKM.mapCommGrp.obj G₀ ≅ G₃ := groupActualScalarExtensionIso c D M
    let bLM : FLM.mapCommGrp.obj G₁ ≅ G₂ := groupActualScalarExtensionIso cL DL M
    let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    let eG := scalarTowerComparisonIso FKM.mapCommGrp FKL.mapCommGrp FLM.mapCommGrp
      eB bL.symm bLM.symm bM
    let eP := scalarTowerComparisonIso FKM FKL FLM e aL.symm aLM.symm aM
    ∀ (T : Over (Spec (CommRingCat.of M)))
      (g : T ⟶ G₂.X) (x : T ⟶ P₂),
      (g • x) ≫ eP.hom = (g ≫ eG.hom.hom.hom.hom) • (x ≫ eP.hom) := by
  intro cL DL FKL FLM FKM G₀ G₁ G₂ G₃ P₀ P₁ P₂ P₃ action₂
    action₃ aL aM aLM bL bM bLM eB eG eP T g x
  exact equivariant_commGrp_tower_comparison_apply FKM FKL FLM e
    G₀ P₀ G₁ P₁ G₂ G₃ P₂ P₃
    bL.symm aL.symm bLM.symm aLM.symm bM aM
    (fun _ a p => picardOneScalarExtensionIso_inv_smul c D L a p)
    (fun _ a p => picardOneScalarExtensionIso_inv_smul cL DL M a p)
    (fun _ a p => picardOneScalarExtensionIso_smul c D M a p) T g x

/-- The group comparison and its action law are constructed together before
specializing the three scalar-extension comparisons to the actual curve. -/
theorem exists_picardOneScalarExtensionTowerGroupIso
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let G₂ := groupScheme (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let G₃ := groupScheme (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let P₀ := picardOne c D
    let P₁ := picardOne cL DL
    let P₂ := picardOne (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let P₃ := picardOne (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let _action₂ : ModObj G₂.X P₂ :=
      picardOneModObj (baseChange L cL M)
        (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let _action₃ : ModObj G₃.X P₃ :=
      picardOneModObj (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let aL : FKL.obj P₀ ≅ P₁ := picardOneScalarExtensionIso c D L
    let aM : FKM.obj P₀ ≅ P₃ := picardOneScalarExtensionIso c D M
    let aLM : FLM.obj P₁ ≅ P₂ := picardOneScalarExtensionIso cL DL M
    let eP := scalarTowerComparisonIso FKM FKL FLM e aL.symm aLM.symm aM
    ∃ eG : G₂ ≅ G₃, ∀ (T : Over (Spec (CommRingCat.of M)))
      (g : T ⟶ G₂.X) (x : T ⟶ P₂),
      (g • x) ≫ eP.hom = (g ≫ eG.hom.hom.hom.hom) • (x ≫ eP.hom) := by
  intro cL DL FKL FLM FKM G₂ G₃ P₀ P₁ P₂ P₃ action₂ action₃ aL aM aLM eP
  let G₀ := groupScheme c D
  let G₁ := groupScheme cL DL
  let bL : FKL.mapCommGrp.obj G₀ ≅ G₁ := groupActualScalarExtensionIso c D L
  let bM : FKM.mapCommGrp.obj G₀ ≅ G₃ := groupActualScalarExtensionIso c D M
  let bLM : FLM.mapCommGrp.obj G₁ ≅ G₂ := groupActualScalarExtensionIso cL DL M
  exact exists_equivariant_commGrp_tower_comparison FKM FKL FLM e
    G₀ P₀ G₁ P₁ G₂ G₃ P₂ P₃
    bL.symm aL.symm bLM.symm aLM.symm bM aM
    (fun _ a p => picardOneScalarExtensionIso_inv_smul c D L a p)
    (fun _ a p => picardOneScalarExtensionIso_inv_smul cL DL M a p)
    (fun _ a p => picardOneScalarExtensionIso_smul c D M a p)

/-- The actual group and Picard-one comparisons for a tower preserve the
torsor action. Successive actions use their native monoidal transports,
and the middle comparison is the existing pullback composition isomorphism. -/
theorem picardOneScalarExtension_tower_smul
    (M : Type u) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    let w : specMap L M ≫ specMap K L = specMap K M := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]
    let e : Over.pullback (specMap K M) ≅
        Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M) :=
      (eqToIso (congrArg
        (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
          Over.pullbackComp (specMap L M) (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let G₀ := groupScheme c D
    let G₁ := groupScheme cL DL
    let G₂ := groupScheme (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let G₃ := groupScheme (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let P₀ := picardOne c D
    let P₁ := picardOne cL DL
    let P₂ := picardOne (baseChange L cL M) (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let P₃ := picardOne (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let _action₂ : ModObj G₂.X P₂ :=
      picardOneModObj (baseChange L cL M)
        (DL.changeBaseOfIdentity (f := cL) (specMap L M))
    let _action₃ : ModObj G₃.X P₃ :=
      picardOneModObj (baseChange K c M) (D.changeBaseOfIdentity (specMap K M))
    let aL : FKL.obj P₀ ≅ P₁ := picardOneScalarExtensionIso c D L
    let aM : FKM.obj P₀ ≅ P₃ := picardOneScalarExtensionIso c D M
    let aLM : FLM.obj P₁ ≅ P₂ := picardOneScalarExtensionIso cL DL M
    let bL : FKL.mapCommGrp.obj G₀ ≅ G₁ := groupActualScalarExtensionIso c D L
    let bM : FKM.mapCommGrp.obj G₀ ≅ G₃ := groupActualScalarExtensionIso c D M
    let bLM : FLM.mapCommGrp.obj G₁ ≅ G₂ := groupActualScalarExtensionIso cL DL M
    let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
    let eG := bLM.symm ≪≫
      FLM.mapCommGrp.mapIso bL.symm ≪≫
        (eB.app G₀).symm ≪≫ bM
    let eP := aLM.symm ≪≫ FLM.mapIso aL.symm ≪≫
      (e.app P₀).symm ≪≫ aM
    ∀ (T : Over (Spec (CommRingCat.of M)))
      (g : T ⟶ G₂.X) (x : T ⟶ P₂),
      (g • x) ≫ eP.hom = (g ≫ eG.hom.hom.hom.hom) • (x ≫ eP.hom) := by
  intro w e
  exact picardOneScalarExtension_tower_smul_of_iso c D L M e



end AlgebraicGeometry.GeneralizedJacobian
