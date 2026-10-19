/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneIntrinsicTorsor
import Nyll.JacobianVarieties.Generalized.PicardOneUnpointedConstruction
import Nyll.JacobianVarieties.Generalized.Construction
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# The intrinsic Picard-one scheme torsor identity over an arbitrary field

The source is the actual constructed generalized Jacobian times the descended
Picard-one scheme. The target is the square of that same Picard-one scheme.
Their isomorphism represents the point-independent raw tensor action and
rigidified difference after fppf sheafification.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

private def representProduct {B : Type u} [Category.{v} B] [HasBinaryProducts B]
    {F G : Bᵒᵖ ⥤ Type (max w v)} {X Y : B}
    (eF : F.RepresentableBy X) (eG : G.RepresentableBy Y) :
    (F ⨯ G).RepresentableBy (X ⨯ Y) :=
  (Functor.RepresentableBy.equivUliftYonedaIso (F ⨯ G) (X ⨯ Y)).symm
    (PreservesLimitPair.iso uliftYoneda.{w} X Y ≪≫
      prod.mapIso (Functor.RepresentableBy.equivUliftYonedaIso F X eF)
        (Functor.RepresentableBy.equivUliftYonedaIso G Y eG))

private theorem representProduct_fst {B : Type u} [Category.{v} B] [HasBinaryProducts B]
    {F G : Bᵒᵖ ⥤ Type (max w v)} {X Y T : B}
    (eF : F.RepresentableBy X) (eG : G.RepresentableBy Y) (x : T ⟶ X ⨯ Y) :
    (prod.fst : F ⨯ G ⟶ F).app (op T) ((representProduct.{u, v, w} eF eG).homEquiv x) =
      eF.homEquiv (x ≫ prod.fst) := by
  let e₁ := Functor.RepresentableBy.equivUliftYonedaIso F X eF
  let e₂ := Functor.RepresentableBy.equivUliftYonedaIso G Y eG
  have h : (PreservesLimitPair.iso uliftYoneda.{w} X Y).hom ≫
      (prod.mapIso e₁ e₂).hom ≫ prod.fst = uliftYoneda.map prod.fst ≫ e₁.hom := by
    rw [prod.mapIso_hom, prod.map_fst, ← Category.assoc,
      PreservesLimitPair.iso_hom, prodComparison_fst]
  let a : ULift.{w} (T ⟶ X ⨯ Y) := ULift.up x
  exact congrArg (fun α : uliftYoneda.{w}.obj (X ⨯ Y) ⟶ F => α.app (op T) a) h

private theorem representSheafProduct_fst
    {B : Type u} [Category.{v} B] [HasBinaryProducts B]
    {J : GrothendieckTopology B}
    [HasBinaryProducts (Sheaf J (Type (max w v)))]
    [PreservesLimitsOfShape (Discrete WalkingPair)
      (sheafToPresheaf J (Type (max w v)))]
    {F G : Sheaf J (Type (max w v))} {X Y T : B}
    (eF : F.obj.RepresentableBy X) (eG : G.obj.RepresentableBy Y)
    (x : T ⟶ X ⨯ Y) :
    (prod.fst : F ⨯ G ⟶ F).hom.app (op T)
      (((representProduct.{u, v, w} eF eG).ofIso
        (PreservesLimitPair.iso (sheafToPresheaf J (Type (max w v))) F G).symm).homEquiv x) =
      eF.homEquiv (x ≫ prod.fst) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (PreservesLimitPair.iso_inv_fst
      (sheafToPresheaf J (Type (max w v))) F G) (op T))
      ((representProduct.{u, v, w} eF eG).homEquiv x)
  exact h.trans (representProduct_fst.{u, v, w} eF eG x)

private theorem representProduct_snd {B : Type u} [Category.{v} B] [HasBinaryProducts B]
    {F G : Bᵒᵖ ⥤ Type (max w v)} {X Y T : B}
    (eF : F.RepresentableBy X) (eG : G.RepresentableBy Y) (x : T ⟶ X ⨯ Y) :
    (prod.snd : F ⨯ G ⟶ G).app (op T) ((representProduct.{u, v, w} eF eG).homEquiv x) =
      eG.homEquiv (x ≫ prod.snd) := by
  let e₁ := Functor.RepresentableBy.equivUliftYonedaIso F X eF
  let e₂ := Functor.RepresentableBy.equivUliftYonedaIso G Y eG
  have h : (PreservesLimitPair.iso uliftYoneda.{w} X Y).hom ≫
      (prod.mapIso e₁ e₂).hom ≫ prod.snd = uliftYoneda.map prod.snd ≫ e₂.hom := by
    rw [prod.mapIso_hom, prod.map_snd, ← Category.assoc,
      PreservesLimitPair.iso_hom, prodComparison_snd]
  let a : ULift.{w} (T ⟶ X ⨯ Y) := ULift.up x
  exact congrArg (fun α : uliftYoneda.{w}.obj (X ⨯ Y) ⟶ G => α.app (op T) a) h

private theorem representSheafProduct_snd
    {B : Type u} [Category.{v} B] [HasBinaryProducts B]
    {J : GrothendieckTopology B}
    [HasBinaryProducts (Sheaf J (Type (max w v)))]
    [PreservesLimitsOfShape (Discrete WalkingPair)
      (sheafToPresheaf J (Type (max w v)))]
    {F G : Sheaf J (Type (max w v))} {X Y T : B}
    (eF : F.obj.RepresentableBy X) (eG : G.obj.RepresentableBy Y)
    (x : T ⟶ X ⨯ Y) :
    (prod.snd : F ⨯ G ⟶ G).hom.app (op T)
      (((representProduct.{u, v, w} eF eG).ofIso
        (PreservesLimitPair.iso (sheafToPresheaf J (Type (max w v))) F G).symm).homEquiv x) =
      eG.homEquiv (x ≫ prod.snd) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (PreservesLimitPair.iso_inv_snd
      (sheafToPresheaf J (Type (max w v))) F G) (op T))
      ((representProduct.{u, v, w} eF eG).homEquiv x)
  exact h.trans (representProduct_snd.{u, v, w} eF eG x)

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual generalized Jacobian times Picard-one represents the product sheaf. -/
def picardOneActionProductRepresentable :
    (modulusPicardZeroSheaf c (modulusCurveMap D) ⨯
      modulusPicardOneSheaf c (modulusCurveMap D)).obj.RepresentableBy
        ((groupScheme c D).X ⨯ picardOne c D) :=
  (representProduct.{u + 1, u, u + 1}
    (picardZeroRepresentable c D) (picardOneRepresentable c D)).ofIso
    (PreservesLimitPair.iso
      (sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (Type (u + 1)))
      (modulusPicardZeroSheaf c (modulusCurveMap D))
      (modulusPicardOneSheaf c (modulusCurveMap D))).symm

/-- The square of the actual descended Picard-one scheme represents its sheaf square. -/
def picardOneSquareRepresentable :
    (modulusPicardOneSheaf c (modulusCurveMap D) ⨯
      modulusPicardOneSheaf c (modulusCurveMap D)).obj.RepresentableBy
        (picardOne c D ⨯ picardOne c D) :=
  (representProduct.{u + 1, u, u + 1}
    (picardOneRepresentable c D) (picardOneRepresentable c D)).ofIso
    (PreservesLimitPair.iso
      (sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (Type (u + 1)))
      (modulusPicardOneSheaf c (modulusCurveMap D))
      (modulusPicardOneSheaf c (modulusCurveMap D))).symm

/-- The first product coordinate is the actual zero class. -/
theorem picardOneActionProductRepresentable_fst
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (groupScheme c D).X ⨯ picardOne c D) :
    (prod.fst : modulusPicardZeroSheaf c (modulusCurveMap D) ⨯
      modulusPicardOneSheaf c (modulusCurveMap D) ⟶ _).hom.app (op T)
        ((picardOneActionProductRepresentable c D).homEquiv x) =
      (picardZeroRepresentable c D).homEquiv (x ≫ prod.fst) :=
  representSheafProduct_fst.{u + 1, u, u + 1}
    (picardZeroRepresentable c D) (picardOneRepresentable c D) x

/-- The second product coordinate is the actual degree-one class. -/
theorem picardOneActionProductRepresentable_snd
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (groupScheme c D).X ⨯ picardOne c D) :
    (prod.snd : modulusPicardZeroSheaf c (modulusCurveMap D) ⨯
      modulusPicardOneSheaf c (modulusCurveMap D) ⟶ _).hom.app (op T)
        ((picardOneActionProductRepresentable c D).homEquiv x) =
      (picardOneRepresentable c D).homEquiv (x ≫ prod.snd) :=
  representSheafProduct_snd.{u + 1, u, u + 1}
    (picardZeroRepresentable c D) (picardOneRepresentable c D) x

/-- The square representation recovers the first actual degree-one class. -/
theorem picardOneSquareRepresentable_fst
    {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ picardOne c D ⨯ picardOne c D) :
    (prod.fst : modulusPicardOneSheaf c (modulusCurveMap D) ⨯
      modulusPicardOneSheaf c (modulusCurveMap D) ⟶ _).hom.app (op T)
        ((picardOneSquareRepresentable c D).homEquiv x) =
      (picardOneRepresentable c D).homEquiv (x ≫ prod.fst) :=
  representSheafProduct_fst.{u + 1, u, u + 1}
    (picardOneRepresentable c D) (picardOneRepresentable c D) x

/-- The scheme torsor identity induced by actual tensor action and rigidified difference. -/
def picardOneTorsorIso :
    (groupScheme c D).X ⨯ picardOne c D ≅ picardOne c D ⨯ picardOne c D :=
  ((picardOneActionProductRepresentable c D).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (Type (u + 1))).mapIso
      (modulusPicardOneSheafTorsorIso c (modulusCurveMap D)))).uniqueUpToIso
        (picardOneSquareRepresentable c D)

/-- The forward map classifies exactly the intrinsic tensor-action sheaf isomorphism. -/
theorem picardOneTorsorIso_classifies
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (groupScheme c D).X ⨯ picardOne c D) :
    (picardOneSquareRepresentable c D).homEquiv (x ≫ (picardOneTorsorIso c D).hom) =
      (modulusPicardOneSheafTorsorIso c (modulusCurveMap D)).hom.hom.app (op T)
        ((picardOneActionProductRepresentable c D).homEquiv x) := by
  let e := (picardOneActionProductRepresentable c D).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (Type (u + 1))).mapIso
      (modulusPicardOneSheafTorsorIso c (modulusCurveMap D)))
  change (picardOneSquareRepresentable c D).homEquiv
    (x ≫ (picardOneSquareRepresentable c D).homEquiv.symm (e.homEquiv (𝟙 _))) =
      e.homEquiv x
  rw [(picardOneSquareRepresentable c D).homEquiv_comp, Equiv.apply_symm_apply]
  exact (e.homEquiv_comp x (𝟙 _)).symm.trans
    (congrArg e.homEquiv (Category.comp_id x))

/-- The actual scheme torsor isomorphism fixes its Picard-one coordinate. -/
theorem picardOneTorsorIso_snd :
    (picardOneTorsorIso c D).hom ≫ prod.snd =
      (prod.snd : (groupScheme c D).X ⨯ picardOne c D ⟶ picardOne c D) := by
  apply (picardOneRepresentable c D).homEquiv.injective
  let x := (picardOneTorsorIso c D).hom
  have hs := representSheafProduct_snd.{u + 1, u, u + 1}
    (picardOneRepresentable c D) (picardOneRepresentable c D) x
  have ht := representSheafProduct_snd.{u + 1, u, u + 1}
    (picardZeroRepresentable c D) (picardOneRepresentable c D) (𝟙 _)
  have hc := picardOneTorsorIso_classifies c D (𝟙 _)
  rw [Category.id_comp] at hc
  have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun v : modulusPicardZeroSheaf c (modulusCurveMap D) ⨯
      modulusPicardOneSheaf c (modulusCurveMap D) ⟶
        modulusPicardOneSheaf c (modulusCurveMap D) => v.hom)
      (modulusPicardOneSheafTorsorIso_snd c (modulusCurveMap D)))
      (op ((groupScheme c D).X ⨯ picardOne c D)))
        ((picardOneActionProductRepresentable c D).homEquiv (𝟙 _))
  exact hs.symm.trans ((congrArg
    ((prod.snd : modulusPicardOneSheaf c (modulusCurveMap D) ⨯
      modulusPicardOneSheaf c (modulusCurveMap D) ⟶ _).hom.app
        (op ((groupScheme c D).X ⨯ picardOne c D))) hc).trans
          (hp.trans (ht.trans (congrArg (picardOneRepresentable c D).homEquiv
            (Category.id_comp prod.snd)))))

/-- The inverse retains the second coordinate as well. -/
theorem picardOneTorsorIso_inv_snd :
    (picardOneTorsorIso c D).inv ≫ prod.snd =
      (prod.snd : picardOne c D ⨯ picardOne c D ⟶ picardOne c D) := by
  rw [← picardOneTorsorIso_snd c D, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The actual action morphism on the descended Picard-one scheme. -/
def picardOneAction : (groupScheme c D).X ⨯ picardOne c D ⟶ picardOne c D :=
  (picardOneTorsorIso c D).hom ≫ prod.fst

/-- The actual rigidified difference morphism on two Picard-one classes. -/
def picardOneDifference : picardOne c D ⨯ picardOne c D ⟶ (groupScheme c D).X :=
  (picardOneTorsorIso c D).inv ≫ prod.fst

end AlgebraicGeometry.GeneralizedJacobian
