/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentAdjunctionUnit
public import Nyll.EtaleCohomology.Descent.SetSheafDescentSourceComposition
public import Nyll.EtaleCohomology.Sites.RepresentablePullback
public import Nyll.EtaleCohomology.Sites.SetPullbackComposition

/-!
# The original second matching arrow

The inverse of the original overlap isomorphism in the second matching
arrow cancels after transporting to the second projection. The remaining
map is the original second-projection unit, through the existing direct
image composition comparison. This keeps the given matching equalizer
and the original counit comparison unchanged.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

private theorem pullbackHomEquiv_of_eq
    {X Y : Scheme.{u}} (a b : Y ⟶ X) (hab : a = b)
    (F : Sheaf X.smallEtaleTopology (Type u))
    (G : Sheaf Y.smallEtaleTopology (Type u))
    (k : (etaleSetPullback b).obj F ⟶ G) :
    (etaleSetPullbackPushforwardAdjunction a).homEquiv _ _
        ((eqToIso (congrArg (fun q => etaleSetPullback q) hab)).hom.app F ≫ k) ≫
      (eqToIso (congrArg (fun q => etaleSetPushforward q) hab)).hom.app G =
        (etaleSetPullbackPushforwardAdjunction b).homEquiv _ _ k := by
  subst b
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id]

private theorem originalOverlap_cancel
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type u)) :
    (etaleSetPullbackCompIso (pullback.fst q q) q).hom.app G ≫
        (SetSheafDescent.overlapComparison q).hom.app G =
      (eqToIso (congrArg (fun r => etaleSetPullback r)
        (pullback.condition (f := q) (g := q)))).hom.app G ≫
          (etaleSetPullbackCompIso (pullback.snd q q) q).hom.app G :=
  congrArg (fun η => η.app G) (SetSheafDescent.overlapComparison_hom_cancellation q)

private theorem adjunction_overlap_cancel
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (A : L ⊣ R)
    {M₁ M₂ : D ⥤ E} {S₁ S₂ : E ⥤ D} (B₁ : M₁ ⊣ S₁) (B₂ : M₂ ⊣ S₂)
    {N₁ N₂ : C ⥤ E} {T₁ T₂ : E ⥤ C} (C₁ : N₁ ⊣ T₁) (C₂ : N₂ ⊣ T₂)
    (e₁ : N₁ ≅ L ⋙ M₁) (e₂ : N₂ ≅ L ⋙ M₂) (e : N₁ ≅ N₂) (d : T₁ ≅ T₂)
    (o : L ⋙ M₁ ≅ L ⋙ M₂)
    (ho : ∀ G : C, e₁.hom.app G ≫ o.hom.app G = e.hom.app G ≫ e₂.hom.app G)
    (c₁ : S₁ ⋙ R ≅ T₁) (c₂ : S₂ ⋙ R ≅ T₂)
    (hc₁ : ∀ (G : C) (H : E) (k : M₁.obj (L.obj G) ⟶ H),
      C₁.homEquiv G H (e₁.hom.app G ≫ k) =
        A.homEquiv G (S₁.obj H) (B₁.homEquiv (L.obj G) H k) ≫ c₁.hom.app H)
    (hc₂ : ∀ (G : C) (H : E) (k : M₂.obj (L.obj G) ⟶ H),
      C₂.homEquiv G H (e₂.hom.app G ≫ k) =
        A.homEquiv G (S₂.obj H) (B₂.homEquiv (L.obj G) H k) ≫ c₂.hom.app H)
    (he : ∀ (G : C) (H : E) (k : N₂.obj G ⟶ H),
      C₁.homEquiv G H (e.hom.app G ≫ k) ≫ d.hom.app H = C₂.homEquiv G H k)
    (F : D) (θ : M₁.obj F ≅ M₂.obj F) :
    (A.comp B₁).homEquiv (R.obj F) (M₁.obj F)
        (o.hom.app (R.obj F) ≫
          M₂.map (A.counit.app F) ≫ θ.inv) ≫
      c₁.hom.app (M₁.obj F) ≫ T₁.map θ.hom ≫ d.hom.app (M₂.obj F) =
        R.map (B₂.unit.app F) ≫ c₂.hom.app (M₂.obj F) := by
  let G := R.obj F
  let F₁ := M₁.obj F
  let F₂ := M₂.obj F
  let oG := o.hom.app G
  let k := M₂.map (A.counit.app F)
  let k₁ := oG ≫ k ≫ θ.inv
  let b := (A.comp B₁).homEquiv G F₁ k₁
  have hcomp₁ : C₁.homEquiv G F₁ (e₁.hom.app G ≫ k₁) =
      b ≫ c₁.hom.app F₁ := by
    dsimp only [b]
    rw [hc₁, Adjunction.comp_homEquiv, Equiv.trans_apply]
  have hoverlap : e₁.hom.app G ≫ oG = e.hom.app G ≫ e₂.hom.app G := ho G
  have hk : (e₁.hom.app G ≫ k₁) ≫ θ.hom =
      e.hom.app G ≫ (e₂.hom.app G ≫ k) := by
    change (e₁.hom.app G ≫ (oG ≫ k ≫ θ.inv)) ≫ θ.hom = _
    rw [Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact (Category.assoc (e₁.hom.app G) oG k).symm.trans
      ((congrArg (fun a => a ≫ k) hoverlap).trans
        (Category.assoc (e.hom.app G) (e₂.hom.app G) k))
  have ht : (b ≫ c₁.hom.app F₁) ≫ T₁.map θ.hom =
      C₁.homEquiv G F₂ (e.hom.app G ≫ (e₂.hom.app G ≫ k)) :=
    (congrArg (fun a => a ≫ T₁.map θ.hom) hcomp₁.symm).trans
      ((C₁.homEquiv_naturality_right (e₁.hom.app G ≫ k₁) θ.hom).symm.trans
        (congrArg (C₁.homEquiv G F₂) hk))
  have hcomp₂ : C₂.homEquiv G F₂ (e₂.hom.app G ≫ k) =
      (A.comp B₂).homEquiv G F₂ k ≫ c₂.hom.app F₂ := by
    rw [hc₂, Adjunction.comp_homEquiv, Equiv.trans_apply]
  have hu : (A.comp B₂).homEquiv G F₂ k = R.map (B₂.unit.app F) :=
    adjunction_composite_homEquiv_map_counit A B₂ F
  change b ≫ c₁.hom.app F₁ ≫ T₁.map θ.hom ≫ d.hom.app F₂ = _
  exact (Category.assoc b (c₁.hom.app F₁) (T₁.map θ.hom ≫ d.hom.app F₂)).symm.trans
    (((Category.assoc (b ≫ c₁.hom.app F₁) (T₁.map θ.hom) (d.hom.app F₂)).symm.trans
      ((congrArg (fun a => a ≫ d.hom.app F₂) ht).trans
        ((he G F₂ (e₂.hom.app G ≫ k)).trans
          (hcomp₂.trans (congrArg (fun a => a ≫ c₂.hom.app F₂) hu))))))

private theorem adjunction_overlap_cancel_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (A : L ⊣ R)
    {M₁ M₂ : D ⥤ E} {S₁ S₂ : E ⥤ D} (B₁ : M₁ ⊣ S₁) (B₂ : M₂ ⊣ S₂)
    {N₁ N₂ : C ⥤ E} {T₁ T₂ : E ⥤ C} (C₁ : N₁ ⊣ T₁) (C₂ : N₂ ⊣ T₂)
    (e₁ : N₁ ≅ L ⋙ M₁) (e₂ : N₂ ≅ L ⋙ M₂) (e : N₁ ≅ N₂) (d : T₁ ≅ T₂)
    (o : L ⋙ M₁ ≅ L ⋙ M₂)
    (ho : ∀ G : C, e₁.hom.app G ≫ o.hom.app G = e.hom.app G ≫ e₂.hom.app G)
    (c₁ : S₁ ⋙ R ≅ T₁) (c₂ : S₂ ⋙ R ≅ T₂)
    (hc₁ : ∀ (G : C) (H : E) (k : M₁.obj (L.obj G) ⟶ H),
      C₁.homEquiv G H (e₁.hom.app G ≫ k) =
        A.homEquiv G (S₁.obj H) (B₁.homEquiv (L.obj G) H k) ≫ c₁.hom.app H)
    (hc₂ : ∀ (G : C) (H : E) (k : M₂.obj (L.obj G) ⟶ H),
      C₂.homEquiv G H (e₂.hom.app G ≫ k) =
        A.homEquiv G (S₂.obj H) (B₂.homEquiv (L.obj G) H k) ≫ c₂.hom.app H)
    (he : ∀ (G : C) (H : E) (k : N₂.obj G ⟶ H),
      C₁.homEquiv G H (e.hom.app G ≫ k) ≫ d.hom.app H = C₂.homEquiv G H k)
    (F : D) (θ : M₁.obj F ≅ M₂.obj F) (H : E) (β : M₂.obj F ⟶ H) :
    (A.comp B₁).homEquiv (R.obj F) (M₁.obj F)
        (o.hom.app (R.obj F) ≫
          M₂.map (A.counit.app F) ≫ θ.inv) ≫
      c₁.hom.app (M₁.obj F) ≫ T₁.map θ.hom ≫ d.hom.app (M₂.obj F) ≫ T₂.map β =
        R.map (B₂.unit.app F ≫ S₂.map β) ≫ c₂.hom.app H := by
  let a := (A.comp B₁).homEquiv (R.obj F) (M₁.obj F)
    (o.hom.app (R.obj F) ≫ M₂.map (A.counit.app F) ≫ θ.inv)
  let u := R.map (B₂.unit.app F)
  let cG := c₂.hom.app (M₂.obj F)
  let cH := c₂.hom.app H
  let m := R.map (S₂.map β)
  let k := T₂.map β
  have hcore : a ≫ c₁.hom.app (M₁.obj F) ≫ T₁.map θ.hom ≫
      d.hom.app (M₂.obj F) = u ≫ cG :=
    adjunction_overlap_cancel A B₁ B₂ C₁ C₂ e₁ e₂ e d o ho
      c₁ c₂ hc₁ hc₂ he F θ
  have hn : m ≫ cH = cG ≫ k := c₂.hom.naturality β
  have hm : R.map (B₂.unit.app F ≫ S₂.map β) = u ≫ m :=
    R.map_comp (B₂.unit.app F) (S₂.map β)
  change a ≫ c₁.hom.app (M₁.obj F) ≫ T₁.map θ.hom ≫
    d.hom.app (M₂.obj F) ≫ k = _
  calc
    a ≫ c₁.hom.app (M₁.obj F) ≫ T₁.map θ.hom ≫ d.hom.app (M₂.obj F) ≫ k =
        (a ≫ c₁.hom.app (M₁.obj F) ≫ T₁.map θ.hom ≫ d.hom.app (M₂.obj F)) ≫ k := by
      simp only [Category.assoc]
    _ = (u ≫ cG) ≫ k := congrArg (fun z => z ≫ k) hcore
    _ = u ≫ (cG ≫ k) := Category.assoc u cG k
    _ = u ≫ (m ≫ cH) := congrArg (fun z => u ≫ z) hn.symm
    _ = (u ≫ m) ≫ cH := (Category.assoc u m cH).symm
    _ = R.map (B₂.unit.app F ≫ S₂.map β) ≫ cH :=
      congrArg (fun z => z ≫ cH) hm.symm

namespace SetSheafDescent

/-- Transporting the actual second matching arrow to the second
projection recovers the original second-projection unit. -/
theorem secondArrow_comp_overlap_pushforward
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (F : Sheaf Y.smallEtaleTopology (Type u))
    (θ : (etaleSetPullback (pullback.fst q q)).obj F ≅
      (etaleSetPullback (pullback.snd q q)).obj F) :
    secondArrow q F θ ≫
        (etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
          ((etaleSetPullback (pullback.fst q q)).obj F) ≫
        (etaleSetPushforward (pullback.fst q q ≫ q)).map θ.hom ≫
        (eqToIso (congrArg (fun r => etaleSetPushforward r)
          (pullback.condition (f := q) (g := q)))).hom.app
            ((etaleSetPullback (pullback.snd q q)).obj F) =
      (etaleSetPushforward q).map
          ((etaleSetPullbackPushforwardAdjunction (pullback.snd q q)).unit.app F) ≫
        (etaleSetPushforwardCompIso (pullback.snd q q) q).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj F) := by
  exact adjunction_overlap_cancel
    (etaleSetPullbackPushforwardAdjunction q)
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q))
    (etaleSetPullbackPushforwardAdjunction (pullback.snd q q))
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q ≫ q))
    (etaleSetPullbackPushforwardAdjunction (pullback.snd q q ≫ q))
    (etaleSetPullbackCompIso (pullback.fst q q) q)
    (etaleSetPullbackCompIso (pullback.snd q q) q)
    (eqToIso (congrArg (fun r => etaleSetPullback r)
      (pullback.condition (f := q) (g := q))))
    (eqToIso (congrArg (fun r => etaleSetPushforward r)
      (pullback.condition (f := q) (g := q))))
    (overlapComparison q) (originalOverlap_cancel q)
    (etaleSetPushforwardCompIso (pullback.fst q q) q)
    (etaleSetPushforwardCompIso (pullback.snd q q) q)
    (fun G H k => pullbackCompIso_hom_homEquiv (pullback.fst q q) q G H k)
    (fun G H k => pullbackCompIso_hom_homEquiv (pullback.snd q q) q G H k)
    (fun G H k => pullbackHomEquiv_of_eq (pullback.fst q q ≫ q)
      (pullback.snd q q ≫ q) (pullback.condition (f := q) (g := q)) G H k)
    F θ

/-- Postcomposing the original second matching arrow with a map from the
second inverse image gives the original second-projection unit followed by
that map. The naturality calculation is made before specializing the adjunctions. -/
theorem secondArrow_comp_overlap_pushforward_map
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (F : Sheaf Y.smallEtaleTopology (Type u))
    (θ : (etaleSetPullback (pullback.fst q q)).obj F ≅
      (etaleSetPullback (pullback.snd q q)).obj F)
    (H : Sheaf (pullback q q).smallEtaleTopology (Type u))
    (β : (etaleSetPullback (pullback.snd q q)).obj F ⟶ H) :
    secondArrow q F θ ≫
        (etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
          ((etaleSetPullback (pullback.fst q q)).obj F) ≫
        (etaleSetPushforward (pullback.fst q q ≫ q)).map θ.hom ≫
        (eqToIso (congrArg (fun r => etaleSetPushforward r)
          (pullback.condition (f := q) (g := q)))).hom.app
            ((etaleSetPullback (pullback.snd q q)).obj F) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map β =
      (etaleSetPushforward q).map
          ((etaleSetPullbackPushforwardAdjunction (pullback.snd q q)).unit.app F ≫
            (etaleSetPushforward (pullback.snd q q)).map β) ≫
        (etaleSetPushforwardCompIso (pullback.snd q q) q).hom.app H := by
  exact adjunction_overlap_cancel_map
    (etaleSetPullbackPushforwardAdjunction q)
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q))
    (etaleSetPullbackPushforwardAdjunction (pullback.snd q q))
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q ≫ q))
    (etaleSetPullbackPushforwardAdjunction (pullback.snd q q ≫ q))
    (etaleSetPullbackCompIso (pullback.fst q q) q)
    (etaleSetPullbackCompIso (pullback.snd q q) q)
    (eqToIso (congrArg (fun r => etaleSetPullback r)
      (pullback.condition (f := q) (g := q))))
    (eqToIso (congrArg (fun r => etaleSetPushforward r)
      (pullback.condition (f := q) (g := q))))
    (overlapComparison q) (originalOverlap_cancel q)
    (etaleSetPushforwardCompIso (pullback.fst q q) q)
    (etaleSetPushforwardCompIso (pullback.snd q q) q)
    (fun G H k => pullbackCompIso_hom_homEquiv (pullback.fst q q) q G H k)
    (fun G H k => pullbackCompIso_hom_homEquiv (pullback.snd q q) q G H k)
    (fun G H k => pullbackHomEquiv_of_eq (pullback.fst q q ≫ q)
      (pullback.snd q q ≫ q) (pullback.condition (f := q) (g := q)) G H k)
    F θ H β

end SetSheafDescent

end EtaleCohomology
