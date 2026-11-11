/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentSecondArrowSections
public import Nyll.EtaleCohomology.Descent.RepresentedOverlapMatchingSections
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSource

public import Nyll.EtaleCohomology.Descent.SetSheafDescentSourceComposition
public import Nyll.EtaleCohomology.Sites.RepresentablePullback
public import Nyll.EtaleCohomology.Sites.SetPullbackComposition
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors

/-!
# Both original matching arrows with represented coefficients

The second arrow retains its original second-projection unit. The first
arrow, under the same actual target comparison, retains the first source
unit followed by the original represented overlap and base equality.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology.SetSheafDescent

private theorem representedIso_hom_comp
    {C : Type*} [Category C] {A B D E : C}
    (β₁ : A ≅ B) (η : B ≅ E) (β₂ : D ≅ E) :
    (β₁ ≪≫ η ≪≫ β₂.symm).hom ≫ β₂.hom = β₁.hom ≫ η.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem represented_first_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : D ⥤ C) (S : E ⥤ D) (T₁ T₂ : E ⥤ C)
    (c : S ⋙ R ≅ T₁) (e : T₁ ≅ T₂)
    {F : D} {G₁ G₂ H₁ H₂ : E}
    (u : F ⟶ S.obj G₁) (θ : G₁ ⟶ G₂)
    (β₁ : G₁ ⟶ H₁) (β₂ : G₂ ⟶ H₂) (η : H₁ ⟶ H₂)
    (hθ : θ ≫ β₂ = β₁ ≫ η) :
    R.map u ≫ c.hom.app G₁ ≫ T₁.map θ ≫ e.hom.app G₂ ≫ T₂.map β₂ =
      R.map (u ≫ S.map β₁) ≫ c.hom.app H₁ ≫ T₁.map η ≫ e.hom.app H₂ := by
  have he : T₁.map β₂ ≫ e.hom.app H₂ = e.hom.app G₂ ≫ T₂.map β₂ :=
    e.hom.naturality β₂
  have hc : R.map (S.map β₁) ≫ c.hom.app H₁ = c.hom.app G₁ ≫ T₁.map β₁ :=
    c.hom.naturality β₁
  have ht : T₁.map θ ≫ T₁.map β₂ = T₁.map β₁ ≫ T₁.map η :=
    (T₁.map_comp θ β₂).symm.trans
      ((congrArg T₁.map hθ).trans (T₁.map_comp β₁ η))
  simp only [Functor.map_comp, Category.assoc]
  rw [← he, ← Category.assoc (T₁.map θ) (T₁.map β₂), ht,
    Category.assoc, ← Category.assoc (c.hom.app G₁) (T₁.map β₁), ← hc]
  simp only [Category.assoc]

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (W : Y.Etale)
  (η : (etaleBaseChange (pullback.fst q q)).obj W ≅
    (etaleBaseChange (pullback.snd q q)).obj W)

/-- The original represented overlap retains its actual Yoneda map
through the existing inverse-image comparisons. -/
theorem representedOverlapIso_hom_comp :
    (representedOverlapIso q W η).hom ≫
        (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom =
      (etaleSetPullbackYonedaObjIso (pullback.fst q q) W).hom ≫
        (pullback q q).smallEtaleTopology.yoneda.map η.hom :=
  representedIso_hom_comp (etaleSetPullbackYonedaObjIso (pullback.fst q q) W)
    ((pullback q q).smallEtaleTopology.yoneda.mapIso η)
    (etaleSetPullbackYonedaObjIso (pullback.snd q q) W)

/-- The original first matching arrow, with the same target comparison
as the original second arrow, is the first source unit followed by the
specified represented overlap and the original equality of base maps. -/
theorem firstArrow_representedOverlapArrowTarget :
    firstArrow q (Y.smallEtaleTopology.yoneda.obj W) ≫
        ((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
    (etaleSetPushforward (pullback.fst q q ≫ q)).map (representedOverlapIso q W η).hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom) =
      (etaleSetPushforward q).map
          ((etaleSetPullbackPushforwardAdjunction (pullback.fst q q)).unit.app
              (Y.smallEtaleTopology.yoneda.obj W) ≫
            (etaleSetPushforward (pullback.fst q q)).map
              (etaleSetPullbackYonedaObjIso (pullback.fst q q) W).hom) ≫
        (etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
          ((pullback q q).smallEtaleTopology.yoneda.obj
            ((etaleBaseChange (pullback.fst q q)).obj W)) ≫
          (etaleSetPushforward (pullback.fst q q ≫ q)).map
            ((pullback q q).smallEtaleTopology.yoneda.map η.hom) ≫
            (eqToIso (congrArg (fun r => etaleSetPushforward r)
              (pullback.condition (f := q) (g := q)))).hom.app
                ((pullback q q).smallEtaleTopology.yoneda.obj
                  ((etaleBaseChange (pullback.snd q q)).obj W)) := by
  let F := Y.smallEtaleTopology.yoneda.obj W
  let θ := representedOverlapIso q W η
  have h₁ := firstArrow_eq_pushforward_unit q F
  have h := represented_first_unit (etaleSetPushforward q)
    (etaleSetPushforward (pullback.fst q q))
    (etaleSetPushforward (pullback.fst q q ≫ q))
    (etaleSetPushforward (pullback.snd q q ≫ q))
    (etaleSetPushforwardCompIso (pullback.fst q q) q)
    (eqToIso (congrArg (fun r => etaleSetPushforward r)
      (pullback.condition (f := q) (g := q))))
    ((etaleSetPullbackPushforwardAdjunction (pullback.fst q q)).unit.app F)
    θ.hom (etaleSetPullbackYonedaObjIso (pullback.fst q q) W).hom
    (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom
    ((pullback q q).smallEtaleTopology.yoneda.map η.hom)
    (representedOverlapIso_hom_comp q W η)
  exact (congrArg (fun k => k ≫ ((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
    (etaleSetPushforward (pullback.fst q q ≫ q)).map θ.hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom)) h₁).trans h

variable {X Z : Scheme.{u}} (f : Z ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (CommRingCat.of Ω) ⟶ X)
  (V : Z.Etale)
  (ψ : (etaleSetPullback (pullback.fst f f)).obj (Z.smallEtaleTopology.yoneda.obj V) ≅
    (etaleSetPullback (pullback.snd f f)).obj (Z.smallEtaleTopology.yoneda.obj V))

/-- The original second arrow becomes the original source pullback on
actual geometric-fiber sections. -/
theorem secondArrow_representedOverlapArrowTarget_fiber :
    (Scheme.pointSmallEtale t).sheafFiber.map
        (secondArrow f (Z.smallEtaleTopology.yoneda.obj V) ψ ≫
          ((etaleSetPushforwardCompIso (pullback.fst f f) f).hom.app
      ((etaleSetPullback (pullback.fst f f)).obj (Z.smallEtaleTopology.yoneda.obj V)) ≫
    (etaleSetPushforward (pullback.fst f f ≫ f)).map ψ.hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := f) (g := f)))).hom.app
          ((etaleSetPullback (pullback.snd f f)).obj (Z.smallEtaleTopology.yoneda.obj V)) ≫
        (etaleSetPushforward (pullback.snd f f ≫ f)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd f f) V).hom)) ≫
      etaleSetPushforwardRepresentableFiberSections
        (pullback.snd f f ≫ f) t ((etaleBaseChange (pullback.snd f f)).obj V) =
    etaleSetPushforwardRepresentableFiberSections f t V ≫
      representedSourcePullback t f (pullback.snd f f) V := by
  let Φ := Scheme.pointSmallEtale t
  let c := etaleSetPushforwardRepresentableFiberSections
    (pullback.snd f f ≫ f) t ((etaleBaseChange (pullback.snd f f)).obj V)
  have h := secondArrow_representedOverlapArrowTarget f V ψ
  exact (congrArg (fun a => Φ.sheafFiber.map a ≫ c) h).trans
    (etaleSetPushforwardRepresentableFiberSections_source
      f (pullback.snd f f) t V)

end EtaleCohomology.SetSheafDescent
