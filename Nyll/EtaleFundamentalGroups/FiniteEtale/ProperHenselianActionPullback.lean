/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianActionLifting
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity
public import Nyll.SchemeTheory.FiniteEtale.RadicialDescentCocycle
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback compatibility of actual proper henselian comparisons

The comparison on the closed fiber is computed using the projections of
the original finite étale covers. These computations keep the specified
closed-fiber identification when the overlap is pulled back.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

section Restriction

variable {X X₀ Y Z A₀ : Scheme.{u}}
  (i : X₀ ⟶ X) (p : Y ⟶ X) (g : Z ⟶ X) (w : A₀ ⟶ Y)
  (u : Z ⟶ Y) (hu : u ≫ p = g)

/-- The actual map from a restricted pullback of the cover to its
restriction over `Y`, induced by the original map over `X`. -/
def coverRestrictionLift :
    Limits.pullback (Limits.pullback.snd w u) (Limits.pullback.fst g i) ⟶
      Limits.pullback w (Limits.pullback.fst p i) :=
  Limits.pullback.lift
    (Limits.pullback.fst (Limits.pullback.snd w u) (Limits.pullback.fst g i) ≫
      Limits.pullback.fst w u)
    (Limits.pullback.snd (Limits.pullback.snd w u) (Limits.pullback.fst g i) ≫
      restrictionLift i p g u hu)
    (by
      rw [Category.assoc, Limits.pullback.condition,
        ← Category.assoc, Limits.pullback.condition]
      simp only [Category.assoc, restrictionLift_fst])

@[reassoc]
theorem coverRestrictionLift_fst :
    coverRestrictionLift i p g w u hu ≫ Limits.pullback.fst w
        (Limits.pullback.fst p i) =
      Limits.pullback.fst (Limits.pullback.snd w u) (Limits.pullback.fst g i) ≫
        Limits.pullback.fst w u :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem coverRestrictionLift_snd :
    coverRestrictionLift i p g w u hu ≫ Limits.pullback.snd w
        (Limits.pullback.fst p i) =
      Limits.pullback.snd (Limits.pullback.snd w u) (Limits.pullback.fst g i) ≫
        restrictionLift i p g u hu :=
  Limits.pullback.lift_snd _ _ _

variable (W : FiniteEtale Y) (V : FiniteEtale X₀)
  (e : (FiniteEtale.pullback (Limits.pullback.fst p i)).obj W ≅
    (FiniteEtale.pullback (Limits.pullback.snd p i)).obj V)

/-- The specified closed-fiber comparison, projected to the original
cover `V`, is the original cover map followed by that same comparison. -/
theorem restrictionIso_hom_left_fst :
    (restrictionIso i p g W V e u hu).hom.left ≫
        Limits.pullback.fst V.hom (Limits.pullback.snd g i) =
      coverRestrictionLift i p g W.hom u hu ≫ e.hom.left ≫
        Limits.pullback.fst V.hom (Limits.pullback.snd p i) := by
  let l := restrictionLift i p g u hu
  let c₁ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) (Limits.pullback.fst g i) u
      (Limits.pullback.fst g i ≫ u) rfl).app W
  let c₂ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) l (Limits.pullback.fst p i)
      (Limits.pullback.fst g i ≫ u) (restrictionLift_fst i p g u hu).symm).app W
  let c₃ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) l (Limits.pullback.snd p i)
      (Limits.pullback.snd g i) (restrictionLift_snd i p g u hu).symm).app V
  let w : W.left ⟶ Y := W.hom
  let v₀ : V.left ⟶ X₀ := V.hom
  let r₁ : Limits.pullback (Limits.pullback.snd w u) (Limits.pullback.fst g i) ⟶
      Limits.pullback w (Limits.pullback.fst g i ≫ u) := c₁.inv.left
  let r₂ : Limits.pullback w (Limits.pullback.fst g i ≫ u) ⟶
      Limits.pullback (Limits.pullback.snd w (Limits.pullback.fst p i)) l := c₂.hom.left
  let r₃ : Limits.pullback (Limits.pullback.snd v₀ (Limits.pullback.snd p i)) l ⟶
      Limits.pullback v₀ (Limits.pullback.snd g i) := c₃.inv.left
  let t : Limits.pullback (Limits.pullback.snd w (Limits.pullback.fst p i)) l ⟶
      Limits.pullback (Limits.pullback.snd v₀ (Limits.pullback.snd p i)) l :=
    ((FiniteEtale.pullback l).map e.hom).left
  let e₀ : Limits.pullback w (Limits.pullback.fst p i) ⟶
      Limits.pullback v₀ (Limits.pullback.snd p i) := e.hom.left
  let v := r₁ ≫ r₂ ≫
    Limits.pullback.fst (Limits.pullback.snd w (Limits.pullback.fst p i)) l
  have hv : v = coverRestrictionLift i p g w u hu := by
    apply Limits.pullback.hom_ext
    · have hc₂ :
          r₂ ≫ Limits.pullback.fst (Limits.pullback.snd w (Limits.pullback.fst p i)) l ≫
              Limits.pullback.fst w (Limits.pullback.fst p i) =
            Limits.pullback.fst w (Limits.pullback.fst g i ≫ u) :=
        pullbackComp_hom_app_left_fst_fst l (Limits.pullback.fst p i)
          (Limits.pullback.fst g i ≫ u) (restrictionLift_fst i p g u hu).symm W
      have hc₁ :
          r₁ ≫ Limits.pullback.fst w (Limits.pullback.fst g i ≫ u) =
            Limits.pullback.fst (Limits.pullback.snd w u) (Limits.pullback.fst g i) ≫
              Limits.pullback.fst w u :=
        pullbackComp_inv_app_left_fst (Limits.pullback.fst g i) u
          (Limits.pullback.fst g i ≫ u) rfl W
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun a => r₁ ≫ a)
          ((Category.assoc _ _ _).trans hc₂)).trans
            (hc₁.trans (coverRestrictionLift_fst i p g w u hu).symm))
    · have hc₂ : r₂ ≫
          Limits.pullback.snd (Limits.pullback.snd w (Limits.pullback.fst p i)) l =
            Limits.pullback.snd w (Limits.pullback.fst g i ≫ u) :=
        MorphismProperty.Over.w c₂.hom
      have hc₁ :
          r₁ ≫ Limits.pullback.snd w (Limits.pullback.fst g i ≫ u) =
            Limits.pullback.snd (Limits.pullback.snd w u) (Limits.pullback.fst g i) :=
        pullbackComp_inv_app_left_snd (Limits.pullback.fst g i) u
          (Limits.pullback.fst g i ≫ u) rfl W
      change (r₁ ≫ r₂ ≫
        Limits.pullback.fst (Limits.pullback.snd w (Limits.pullback.fst p i)) l) ≫
          Limits.pullback.snd w (Limits.pullback.fst p i) = _
      rw [Category.assoc, Category.assoc, Limits.pullback.condition,
        ← Category.assoc r₂, hc₂, ← Category.assoc, hc₁, coverRestrictionLift_snd]
  have hmap :
      t ≫ Limits.pullback.fst (Limits.pullback.snd v₀ (Limits.pullback.snd p i)) l =
        Limits.pullback.fst (Limits.pullback.snd w (Limits.pullback.fst p i)) l ≫ e₀ :=
    Limits.pullback.lift_fst _ _ _
  have hc₃ :
      r₃ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd g i) =
        Limits.pullback.fst (Limits.pullback.snd v₀ (Limits.pullback.snd p i)) l ≫
          Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
    pullbackComp_inv_app_left_fst l (Limits.pullback.snd p i)
      (Limits.pullback.snd g i) (restrictionLift_snd i p g u hu).symm V
  have hfinal : ((r₁ ≫ r₂) ≫ t ≫ r₃) ≫
        Limits.pullback.fst v₀ (Limits.pullback.snd g i) =
      coverRestrictionLift i p g w u hu ≫ e₀ ≫
        Limits.pullback.fst v₀ (Limits.pullback.snd p i) := by
    have ht :
        (t ≫ r₃) ≫ Limits.pullback.fst v₀ (Limits.pullback.snd g i) =
          (Limits.pullback.fst (Limits.pullback.snd w (Limits.pullback.fst p i)) l ≫
            e₀) ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => t ≫ k) hc₃).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫
              Limits.pullback.fst v₀ (Limits.pullback.snd p i)) hmap)))
    calc
      _ = (r₁ ≫ r₂) ≫
          ((Limits.pullback.fst (Limits.pullback.snd w (Limits.pullback.fst p i)) l ≫
            e₀) ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i)) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => (r₁ ≫ r₂) ≫ k) ht)
      _ = ((r₁ ≫ r₂) ≫
          Limits.pullback.fst (Limits.pullback.snd w (Limits.pullback.fst p i)) l) ≫
            e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
        (congrArg (fun k => (r₁ ≫ r₂) ≫ k) (Category.assoc _ _ _)).trans
          (Category.assoc _ _ _).symm
      _ = v ≫ e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
        congrArg (fun k => k ≫ e₀ ≫
          Limits.pullback.fst v₀ (Limits.pullback.snd p i)) (Category.assoc _ _ _)
      _ = _ := congrArg (fun k => k ≫ e₀ ≫
        Limits.pullback.fst v₀ (Limits.pullback.snd p i)) hv
  exact hfinal

end Restriction

section Reindex

variable {Y Z T : Scheme.{u}} (W : FiniteEtale Y)
  {u v : Z ⟶ Y}
  (c : (FiniteEtale.pullback u).obj W ≅ (FiniteEtale.pullback v).obj W)
  (h : T ⟶ Z) (a b : T ⟶ Y) (ha : a = h ≫ u) (hb : b = h ≫ v)

/-- Reindex the actual comparison using the existing canonical pullback
composition isomorphisms and the specified composite maps. -/
def reindexIso : (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W :=
  (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h u a ha).app W ≪≫
      (FiniteEtale.pullback h).mapIso c ≪≫
        ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) h v b hb).app W).symm

/-- Reindexing preserves the actual projection into the original
comparison, before passing to the ultimate covering scheme. -/
theorem reindexIso_hom_projection :
    (reindexIso W c h a b ha hb).hom.left ≫
        ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) h v b hb).hom.app W).left ≫
        Limits.pullback.fst ((FiniteEtale.pullback v).obj W).hom h =
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) h u a ha).hom.app W).left ≫
        Limits.pullback.fst ((FiniteEtale.pullback u).obj W).hom h ≫ c.hom.left := by
  let c₁ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h u a ha).app W
  let c₂ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h v b hb).app W
  have hx : (reindexIso W c h a b ha hb).hom ≫ c₂.hom =
      c₁.hom ≫ (FiniteEtale.pullback h).map c.hom := by
    change ((c₁.hom ≫ (FiniteEtale.pullback h).map c.hom) ≫ c₂.inv) ≫ c₂.hom = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (c₁.hom ≫ (FiniteEtale.pullback h).map c.hom) ≫ k)
        c₂.inv_hom_id).trans (Category.comp_id _))
  have hx' :
      (reindexIso W c h a b ha hb).hom.left ≫ c₂.hom.left =
        c₁.hom.left ≫ ((FiniteEtale.pullback h).map c.hom).left :=
    congrArg (fun k => k.left) hx
  have hm :
      ((FiniteEtale.pullback h).map c.hom).left ≫
          Limits.pullback.fst ((FiniteEtale.pullback v).obj W).hom h =
        Limits.pullback.fst ((FiniteEtale.pullback u).obj W).hom h ≫ c.hom.left :=
    Limits.pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫
      Limits.pullback.fst ((FiniteEtale.pullback v).obj W).hom h) hx').trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => c₁.hom.left ≫ k) hm)))

/-- The original covering-scheme projection of the reindexed map is
given by the canonical comparison and the original overlap map. -/
theorem reindexIso_hom_left_fst :
    (reindexIso W c h a b ha hb).hom.left ≫ Limits.pullback.fst W.hom b =
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) h u a ha).hom.app W).left ≫
        Limits.pullback.fst ((FiniteEtale.pullback u).obj W).hom h ≫
          c.hom.left ≫ Limits.pullback.fst W.hom v := by
  let ra : Limits.pullback W.hom a ⟶
      Limits.pullback (Limits.pullback.snd W.hom u) h :=
    ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) h u a ha).hom.app W).left
  let rb : Limits.pullback W.hom b ⟶
      Limits.pullback (Limits.pullback.snd W.hom v) h :=
    ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) h v b hb).hom.app W).left
  let k : Limits.pullback W.hom a ⟶ Limits.pullback W.hom b :=
    (reindexIso W c h a b ha hb).hom.left
  let d : Limits.pullback W.hom u ⟶ Limits.pullback W.hom v := c.hom.left
  have hv : rb ≫ Limits.pullback.fst (Limits.pullback.snd W.hom v) h ≫
      Limits.pullback.fst W.hom v = Limits.pullback.fst W.hom b :=
    pullbackComp_hom_app_left_fst_fst h v b hb W
  have he : k ≫ rb ≫ Limits.pullback.fst (Limits.pullback.snd W.hom v) h =
      ra ≫ Limits.pullback.fst (Limits.pullback.snd W.hom u) h ≫ d :=
    reindexIso_hom_projection W c h a b ha hb
  have hp := congrArg (fun z => z ≫ Limits.pullback.fst W.hom v) he
  have hl :
      (k ≫ rb ≫ Limits.pullback.fst (Limits.pullback.snd W.hom v) h) ≫
          Limits.pullback.fst W.hom v =
        k ≫ Limits.pullback.fst W.hom b :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => k ≫ z)
        ((Category.assoc _ _ _).trans hv))
  exact hl.symm.trans (hp.trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z => ra ≫ z) (Category.assoc _ _ _))))

end Reindex

section RestrictionComposition

variable {X X₀ Y Z T : Scheme.{u}}
  (i : X₀ ⟶ X) (p : Y ⟶ X) (g : Z ⟶ X)
  (u : Z ⟶ Y) (hu : u ≫ p = g)
  (h : T ⟶ Z) (a : T ⟶ Y) (ha : a = h ≫ u)

include hu ha in
/-- The composite cover map lies over the composite base map. -/
theorem composite_over : a ≫ p = h ≫ g := by
  rw [ha, Category.assoc, hu]

/-- Restricting the original composite map agrees with the composite of
the two original restricted maps, by the actual cartesian projections. -/
theorem restrictionLift_comp :
    restrictionLift i g (h ≫ g) h rfl ≫ restrictionLift i p g u hu =
      restrictionLift i p (h ≫ g) a (composite_over p g u hu h a ha) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, restrictionLift_fst, ← Category.assoc,
      restrictionLift_fst, Category.assoc, ← ha, restrictionLift_fst]
  · rw [Category.assoc, restrictionLift_snd, restrictionLift_snd, restrictionLift_snd]

private theorem coverRestrictionLift_naturality {A : Scheme.{u}} (w : A ⟶ Y)
    (K : Limits.pullback w a ⟶ Limits.pullback w u)
    (hK₁ : K ≫ Limits.pullback.fst w u = Limits.pullback.fst w a)
    (hK₂ : K ≫ Limits.pullback.snd w u = Limits.pullback.snd w a ≫ h) :
    let h₀ := restrictionLift i g (h ≫ g) h rfl
    let K₀ := Limits.pullback.map (Limits.pullback.snd w a)
      (Limits.pullback.fst (h ≫ g) i) (Limits.pullback.snd w u)
      (Limits.pullback.fst g i) K h₀ h hK₂.symm
        (restrictionLift_fst i g (h ≫ g) h rfl).symm
    K₀ ≫ coverRestrictionLift i p g w u hu =
      coverRestrictionLift i p (h ≫ g) w a (composite_over p g u hu h a ha) := by
  intro h₀ K₀
  have h₁ :
      K₀ ≫ Limits.pullback.fst (Limits.pullback.snd w u) (Limits.pullback.fst g i) =
        Limits.pullback.fst (Limits.pullback.snd w a) (Limits.pullback.fst (h ≫ g) i) ≫
          K := Limits.pullback.lift_fst _ _ _
  have h₂ :
      K₀ ≫ Limits.pullback.snd (Limits.pullback.snd w u) (Limits.pullback.fst g i) =
        Limits.pullback.snd (Limits.pullback.snd w a) (Limits.pullback.fst (h ≫ g) i) ≫
          h₀ := Limits.pullback.lift_snd _ _ _
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, coverRestrictionLift_fst, ← Category.assoc, h₁,
      Category.assoc, hK₁, coverRestrictionLift_fst]
  · rw [Category.assoc, coverRestrictionLift_snd, ← Category.assoc, h₂,
      Category.assoc, restrictionLift_comp i p g u hu h a ha, coverRestrictionLift_snd]

end RestrictionComposition

section ComparisonCompatibility

variable {X X₀ Y Z T : Scheme.{u}}
  (i : X₀ ⟶ X) (p : Y ⟶ X) (g : Z ⟶ X)
  (W : FiniteEtale Y) (V : FiniteEtale X₀)
  (e : (FiniteEtale.pullback (Limits.pullback.fst p i)).obj W ≅
    (FiniteEtale.pullback (Limits.pullback.snd p i)).obj V)
  (u v : Z ⟶ Y) (hu : u ≫ p = g) (hv : v ≫ p = g)
  (c : (FiniteEtale.pullback u).obj W ≅ (FiniteEtale.pullback v).obj W)
  (h : T ⟶ Z) (a b : T ⟶ Y) (ha : a = h ≫ u) (hb : b = h ≫ v)

private theorem restrictionIso_reindex_compatibility
    (hc :
      (FiniteEtale.pullback (Limits.pullback.fst g i)).map c.hom ≫
          (restrictionIso i p g W V e v hv).hom =
        (restrictionIso i p g W V e u hu).hom) :
    (FiniteEtale.pullback (Limits.pullback.fst (h ≫ g) i)).map
        (reindexIso W c h a b ha hb).hom ≫
      (restrictionIso i p (h ≫ g) W V e b (composite_over p g v hv h b hb)).hom =
    (restrictionIso i p (h ≫ g) W V e a (composite_over p g u hu h a ha)).hom := by
  let w : W.left ⟶ Y := W.hom
  let v₀ : V.left ⟶ X₀ := V.hom
  let iz : Limits.pullback g i ⟶ Z := Limits.pullback.fst g i
  let it : Limits.pullback (h ≫ g) i ⟶ T := Limits.pullback.fst (h ≫ g) i
  let h₀ : Limits.pullback (h ≫ g) i ⟶ Limits.pullback g i :=
    restrictionLift i g (h ≫ g) h rfl
  let ca := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h u a ha).app W
  let cb := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h v b hb).app W
  let ra : Limits.pullback w a ⟶ Limits.pullback (Limits.pullback.snd w u) h :=
    ca.hom.left
  let rb : Limits.pullback w b ⟶ Limits.pullback (Limits.pullback.snd w v) h :=
    cb.hom.left
  let K : Limits.pullback w a ⟶ Limits.pullback w u :=
    ra ≫ Limits.pullback.fst (Limits.pullback.snd w u) h
  let L : Limits.pullback w b ⟶ Limits.pullback w v :=
    rb ≫ Limits.pullback.fst (Limits.pullback.snd w v) h
  have hK₁ : K ≫ Limits.pullback.fst w u = Limits.pullback.fst w a :=
    (Category.assoc _ _ _).trans (pullbackComp_hom_app_left_fst_fst h u a ha W)
  have hL₁ : L ≫ Limits.pullback.fst w v = Limits.pullback.fst w b :=
    (Category.assoc _ _ _).trans (pullbackComp_hom_app_left_fst_fst h v b hb W)
  have hra : ra ≫ Limits.pullback.snd (Limits.pullback.snd w u) h =
      Limits.pullback.snd w a := MorphismProperty.Over.w ca.hom
  have hrb : rb ≫ Limits.pullback.snd (Limits.pullback.snd w v) h =
      Limits.pullback.snd w b := MorphismProperty.Over.w cb.hom
  have hK₂ : K ≫ Limits.pullback.snd w u = Limits.pullback.snd w a ≫ h := by
    change (ra ≫ Limits.pullback.fst (Limits.pullback.snd w u) h) ≫
      Limits.pullback.snd w u = _
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hra]
  have hL₂ : L ≫ Limits.pullback.snd w v = Limits.pullback.snd w b ≫ h := by
    change (rb ≫ Limits.pullback.fst (Limits.pullback.snd w v) h) ≫
      Limits.pullback.snd w v = _
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hrb]
  let K₀ := Limits.pullback.map (Limits.pullback.snd w a) it
    (Limits.pullback.snd w u) iz K h₀ h hK₂.symm
      (restrictionLift_fst i g (h ≫ g) h rfl).symm
  let L₀ := Limits.pullback.map (Limits.pullback.snd w b) it
    (Limits.pullback.snd w v) iz L h₀ h hL₂.symm
      (restrictionLift_fst i g (h ≫ g) h rfl).symm
  let cz : Limits.pullback w u ⟶ Limits.pullback w v := c.hom.left
  let ct : Limits.pullback w a ⟶ Limits.pullback w b :=
    (reindexIso W c h a b ha hb).hom.left
  let cz₀ : Limits.pullback (Limits.pullback.snd w u) iz ⟶
      Limits.pullback (Limits.pullback.snd w v) iz :=
    ((FiniteEtale.pullback iz).map c.hom).left
  let ct₀ : Limits.pullback (Limits.pullback.snd w a) it ⟶
      Limits.pullback (Limits.pullback.snd w b) it :=
    ((FiniteEtale.pullback it).map (reindexIso W c h a b ha hb).hom).left
  have hKL : ct ≫ L = K ≫ cz := by
    exact (reindexIso_hom_projection W c h a b ha hb).trans (Category.assoc _ _ _).symm
  have hK₀₁ : K₀ ≫ Limits.pullback.fst (Limits.pullback.snd w u) iz =
      Limits.pullback.fst (Limits.pullback.snd w a) it ≫ K :=
    Limits.pullback.lift_fst _ _ _
  have hL₀₁ : L₀ ≫ Limits.pullback.fst (Limits.pullback.snd w v) iz =
      Limits.pullback.fst (Limits.pullback.snd w b) it ≫ L :=
    Limits.pullback.lift_fst _ _ _
  have hK₀₂ : K₀ ≫ Limits.pullback.snd (Limits.pullback.snd w u) iz =
      Limits.pullback.snd (Limits.pullback.snd w a) it ≫ h₀ :=
    Limits.pullback.lift_snd _ _ _
  have hL₀₂ : L₀ ≫ Limits.pullback.snd (Limits.pullback.snd w v) iz =
      Limits.pullback.snd (Limits.pullback.snd w b) it ≫ h₀ :=
    Limits.pullback.lift_snd _ _ _
  have hcz₁ : cz₀ ≫ Limits.pullback.fst (Limits.pullback.snd w v) iz =
      Limits.pullback.fst (Limits.pullback.snd w u) iz ≫ cz :=
    Limits.pullback.lift_fst _ _ _
  have hct₁ : ct₀ ≫ Limits.pullback.fst (Limits.pullback.snd w b) it =
      Limits.pullback.fst (Limits.pullback.snd w a) it ≫ ct :=
    Limits.pullback.lift_fst _ _ _
  have hcz₂ : cz₀ ≫ Limits.pullback.snd (Limits.pullback.snd w v) iz =
      Limits.pullback.snd (Limits.pullback.snd w u) iz :=
    Limits.pullback.lift_snd _ _ _
  have hct₂ : ct₀ ≫ Limits.pullback.snd (Limits.pullback.snd w b) it =
      Limits.pullback.snd (Limits.pullback.snd w a) it :=
    Limits.pullback.lift_snd _ _ _
  have hKL₀ : ct₀ ≫ L₀ = K₀ ≫ cz₀ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hL₀₁, ← Category.assoc, hct₁,
        Category.assoc, hKL, ← Category.assoc, ← hK₀₁,
        Category.assoc, ← hcz₁, ← Category.assoc]
    · rw [Category.assoc, hL₀₂, ← Category.assoc, hct₂,
        Category.assoc, hcz₂, hK₀₂]
  let zu := coverRestrictionLift i p g w u hu
  let zv := coverRestrictionLift i p g w v hv
  let tu := coverRestrictionLift i p (h ≫ g) w a (composite_over p g u hu h a ha)
  let tv := coverRestrictionLift i p (h ≫ g) w b (composite_over p g v hv h b hb)
  have hKres : K₀ ≫ zu = tu :=
    coverRestrictionLift_naturality i p g u hu h a ha w K hK₁ hK₂
  have hLres : L₀ ≫ zv = tv :=
    coverRestrictionLift_naturality i p g v hv h b hb w L hL₁ hL₂
  let e₀ : Limits.pullback w (Limits.pullback.fst p i) ⟶
      Limits.pullback v₀ (Limits.pullback.snd p i) := e.hom.left
  let ru : Limits.pullback (Limits.pullback.snd w u) iz ⟶
      Limits.pullback v₀ (Limits.pullback.snd g i) :=
    (restrictionIso i p g W V e u hu).hom.left
  let rv : Limits.pullback (Limits.pullback.snd w v) iz ⟶
      Limits.pullback v₀ (Limits.pullback.snd g i) :=
    (restrictionIso i p g W V e v hv).hom.left
  let su : Limits.pullback (Limits.pullback.snd w a) it ⟶
      Limits.pullback v₀ (Limits.pullback.snd (h ≫ g) i) :=
    (restrictionIso i p (h ≫ g) W V e a (composite_over p g u hu h a ha)).hom.left
  let sv : Limits.pullback (Limits.pullback.snd w b) it ⟶
      Limits.pullback v₀ (Limits.pullback.snd (h ≫ g) i) :=
    (restrictionIso i p (h ≫ g) W V e b (composite_over p g v hv h b hb)).hom.left
  have hru : ru ≫ Limits.pullback.fst v₀ (Limits.pullback.snd g i) =
      zu ≫ e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
    restrictionIso_hom_left_fst i p g u hu W V e
  have hrv : rv ≫ Limits.pullback.fst v₀ (Limits.pullback.snd g i) =
      zv ≫ e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
    restrictionIso_hom_left_fst i p g v hv W V e
  have hsu : su ≫ Limits.pullback.fst v₀ (Limits.pullback.snd (h ≫ g) i) =
      tu ≫ e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
    restrictionIso_hom_left_fst i p (h ≫ g) a
      (composite_over p g u hu h a ha) W V e
  have hsv : sv ≫ Limits.pullback.fst v₀ (Limits.pullback.snd (h ≫ g) i) =
      tv ≫ e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) :=
    restrictionIso_hom_left_fst i p (h ≫ g) b
      (composite_over p g v hv h b hb) W V e
  have hcr : cz₀ ≫ rv = ru := congrArg (fun k => k.left) hc
  have hcr' :
      cz₀ ≫ zv ≫ e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) =
        zu ≫ e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i) := by
    rw [← hrv, ← Category.assoc, hcr, hru]
  apply MorphismProperty.Over.Hom.ext
  change ct₀ ≫ sv = su
  apply Limits.pullback.hom_ext
  · let t := e₀ ≫ Limits.pullback.fst v₀ (Limits.pullback.snd p i)
    have heq : ct₀ ≫ tv ≫ t = tu ≫ t := by
      calc
        _ = ct₀ ≫ (L₀ ≫ zv) ≫ t :=
          congrArg (fun k => ct₀ ≫ k ≫ t) hLres.symm
        _ = (ct₀ ≫ L₀) ≫ zv ≫ t :=
          (congrArg (fun k => ct₀ ≫ k) (Category.assoc _ _ _)).trans
            (Category.assoc _ _ _).symm
        _ = (K₀ ≫ cz₀) ≫ zv ≫ t :=
          congrArg (fun k => k ≫ zv ≫ t) hKL₀
        _ = K₀ ≫ zu ≫ t :=
          (Category.assoc _ _ _).trans (congrArg (fun k => K₀ ≫ k) hcr')
        _ = _ :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ t) hKres)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => ct₀ ≫ k) hsv).trans (heq.trans hsu.symm))
  · have hsu₂ : su ≫ Limits.pullback.snd v₀ (Limits.pullback.snd (h ≫ g) i) =
        Limits.pullback.snd (Limits.pullback.snd w a) it :=
      MorphismProperty.Over.w
        (restrictionIso i p (h ≫ g) W V e a (composite_over p g u hu h a ha)).hom
    have hsv₂ : sv ≫ Limits.pullback.snd v₀ (Limits.pullback.snd (h ≫ g) i) =
        Limits.pullback.snd (Limits.pullback.snd w b) it :=
      MorphismProperty.Over.w
        (restrictionIso i p (h ≫ g) W V e b (composite_over p g v hv h b hb)).hom
    rw [Category.assoc, hsv₂, hct₂, hsu₂]

end ComparisonCompatibility

section Proper

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X Y Z T : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (p : Y ⟶ X) (g : Z ⟶ X) [IsProper (g ≫ f)] (W : FiniteEtale Y)

/-- Pulling back the original lifted comparison agrees with the unique
comparison lifted on the new proper source. The original cover and its
specified closed-fiber identification occur on both sides. -/
theorem liftedIso_pullback :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    ∀ (V : FiniteEtale X₀) (e : P.obj W ≅ Q.obj V)
      (u v : Z ⟶ Y) (hu : u ≫ p = g) (hv : v ≫ p = g)
      (h : T ⟶ Z) [IsProper ((h ≫ g) ≫ f)]
      (a b : T ⟶ Y) (ha : a = h ≫ u) (hb : b = h ≫ v),
      reindexIso (u := u) (v := v) W
          (liftedIso (R := R) (X := X) (Y := Y) (Z := Z) f p g W V e u hu v hv)
          h a b ha hb =
        liftedIso (R := R) (X := X) (Y := Y) (Z := T) f p (h ≫ g) W V e
          a (composite_over p g u hu h a ha) b (composite_over p g v hv h b hb) := by
  intro r X₀ i Y₀ P Q V e u v hu hv h hh a b ha hb
  let Z₀ : Scheme.{u} := Limits.pullback g i
  let T₀ : Scheme.{u} := Limits.pullback (h ≫ g) i
  let Fz : FiniteEtale Z ⥤ FiniteEtale Z₀ :=
    FiniteEtale.pullback (Limits.pullback.fst g i)
  let Ft : FiniteEtale T ⥤ FiniteEtale T₀ :=
    FiniteEtale.pullback (Limits.pullback.fst (h ≫ g) i)
  let cz : (FiniteEtale.pullback u).obj W ≅ (FiniteEtale.pullback v).obj W :=
    liftedIso (R := R) (X := X) (Y := Y) (Z := Z) f p g W V e u hu v hv
  let ct : (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W :=
    liftedIso (R := R) (X := X) (Y := Y) (Z := T) f p (h ≫ g) W V e
      a (composite_over p g u hu h a ha) b (composite_over p g v hv h b hb)
  let zu := restrictionIso i p g W V e u hu
  let zv := restrictionIso i p g W V e v hv
  let tu := restrictionIso i p (h ≫ g) W V e a (composite_over p g u hu h a ha)
  let tv := restrictionIso i p (h ≫ g) W V e b (composite_over p g v hv h b hb)
  have hz : Fz.map cz.hom = zu.hom ≫ zv.inv :=
    liftedIso_hom_restrict f p g W V e u hu v hv
  have ht : Ft.map ct.hom = tu.hom ≫ tv.inv :=
    liftedIso_hom_restrict f p (h ≫ g) W V e
      a (composite_over p g u hu h a ha) b (composite_over p g v hv h b hb)
  have hz' : Fz.map cz.hom ≫ zv.hom = zu.hom := by
    exact (congrArg (fun k => k ≫ zv.hom) hz).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => zu.hom ≫ k) zv.inv_hom_id).trans
          (Category.comp_id _)))
  have ht' : Ft.map ct.hom ≫ tv.hom = tu.hom := by
    exact (congrArg (fun k => k ≫ tv.hom) ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => tu.hom ≫ k) tv.inv_hom_id).trans
          (Category.comp_id _)))
  let FF : Ft.FullyFaithful := closedFiberPullbackFullyFaithful f (h ≫ g)
  apply Iso.ext
  apply FF.map_injective
  apply (cancel_mono tv.hom).mp
  exact (restrictionIso_reindex_compatibility i p g W V e
    u v hu hv cz h a b ha hb hz').trans ht'.symm

private theorem liftedIso_pullback_over :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    ∀ (V : FiniteEtale X₀) (e : P.obj W ≅ Q.obj V)
      (u v : Z ⟶ Y) (hu : u ≫ p = g) (hv : v ≫ p = g)
      (h : T ⟶ Z) (gT : T ⟶ X) [IsProper (gT ≫ f)]
      (_hgT : gT = h ≫ g)
      (a b : T ⟶ Y) (ha : a = h ≫ u) (hb : b = h ≫ v)
      (haT : a ≫ p = gT) (hbT : b ≫ p = gT),
      reindexIso (u := u) (v := v) W
          (liftedIso (R := R) (X := X) (Y := Y) (Z := Z) f p g W V e u hu v hv)
          h a b ha hb =
        liftedIso (R := R) (X := X) (Y := Y) (Z := T) f p gT W V e
          a haT b hbT := by
  intro r X₀ i Y₀ P Q V e u v hu hv h gT hproper hgT a b ha hb haT hbT
  subst gT
  exact liftedIso_pullback (R := R) (X := X) (Y := Y) (Z := Z) (T := T)
    f p g W V e u v hu hv h a b ha hb

end Proper

section DoubleOverlap

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (p : Y ⟶ X) [IsProper p] (W : FiniteEtale Y)

/-- The actual double-overlap comparison satisfies the cocycle after
reindexing along the three pair projections of the original triple
fiber product. Its closed-fiber identification is retained throughout. -/
theorem doubleOverlapIso_triple_cocycle :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    ∀ (V : FiniteEtale X₀) (e : P.obj W ≅ Q.obj V),
      let a := radicialTripleFirst p
      let b := radicialTripleSecond p
      let c := radicialTripleThird p
      let kab := Limits.pullback.lift a b (radicialTriple_first_second p)
      let kbc := Limits.pullback.lift b c (radicialTriple_second_third p)
      let kac := Limits.pullback.lift a c (radicialTriple_first_third p)
      let θ := doubleOverlapIso f p W V e
      reindexIso W θ kab a b
          (Limits.pullback.lift_fst _ _ _).symm
          (Limits.pullback.lift_snd _ _ _).symm ≪≫
        reindexIso W θ kbc b c
          (Limits.pullback.lift_fst _ _ _).symm
          (Limits.pullback.lift_snd _ _ _).symm =
      reindexIso W θ kac a c
        (Limits.pullback.lift_fst _ _ _).symm
        (Limits.pullback.lift_snd _ _ _).symm := by
  intro r X₀ i Y₀ P Q V e a b c kab kbc kac θ
  let D : Scheme.{u} := Limits.pullback p p
  let gD : D ⟶ X := Limits.pullback.fst p p ≫ p
  let gT : radicialTriple p ⟶ X := a ≫ p
  have hD : IsProper (gD ≫ f) := inferInstance
  have haProper : IsProper a := inferInstanceAs (IsProper
    (Limits.pullback.fst (Limits.pullback.fst p p) (Limits.pullback.fst p p) ≫
      Limits.pullback.fst p p))
  have hT : IsProper (gT ≫ f) := inferInstance
  have haT : a ≫ p = gT := rfl
  have hbT : b ≫ p = gT := (radicialTriple_first_second p).symm
  have hcT : c ≫ p = gT := (radicialTriple_first_third p).symm
  have hkab : gT = kab ≫ gD :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ p)
        (Limits.pullback.lift_fst a b (radicialTriple_first_second p)))).symm
  have hkbc : gT = kbc ≫ gD :=
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ p)
        (Limits.pullback.lift_fst b c (radicialTriple_second_third p)))).trans hbT).symm
  have hkac : gT = kac ≫ gD :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ p)
        (Limits.pullback.lift_fst a c (radicialTriple_first_third p)))).symm
  have hab :
      reindexIso W θ kab a b
        (Limits.pullback.lift_fst _ _ _).symm
        (Limits.pullback.lift_snd _ _ _).symm =
      liftedIso (R := R) f p gT W V e a haT b hbT :=
    liftedIso_pullback_over (R := R) (X := X) (Y := Y) (Z := D)
      (T := radicialTriple p) f p gD W V e
      (Limits.pullback.fst p p) (Limits.pullback.snd p p) rfl
      Limits.pullback.condition.symm kab gT hkab a b
      (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm haT hbT
  have hbc :
      reindexIso W θ kbc b c
        (Limits.pullback.lift_fst _ _ _).symm
        (Limits.pullback.lift_snd _ _ _).symm =
      liftedIso (R := R) f p gT W V e b hbT c hcT :=
    liftedIso_pullback_over (R := R) (X := X) (Y := Y) (Z := D)
      (T := radicialTriple p) f p gD W V e
      (Limits.pullback.fst p p) (Limits.pullback.snd p p) rfl
      Limits.pullback.condition.symm kbc gT hkbc b c
      (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm hbT hcT
  have hac :
      reindexIso W θ kac a c
        (Limits.pullback.lift_fst _ _ _).symm
        (Limits.pullback.lift_snd _ _ _).symm =
      liftedIso (R := R) f p gT W V e a haT c hcT :=
    liftedIso_pullback_over (R := R) (X := X) (Y := Y) (Z := D)
      (T := radicialTriple p) f p gD W V e
      (Limits.pullback.fst p p) (Limits.pullback.snd p p) rfl
      Limits.pullback.condition.symm kac gT hkac a c
      (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm haT hcT
  exact (congrArg₂ (fun x y => x ≪≫ y) hab hbc).trans
    ((liftedIso_trans (R := R) f p gT W V e a haT b hbT c hcT).trans hac.symm)

/-- On the actual diagonal, the original overlap comparison becomes the
identity of the native identity pullback of the original cover. -/
theorem doubleOverlapIso_diagonal :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    ∀ (V : FiniteEtale X₀) (e : P.obj W ≅ Q.obj V),
      reindexIso W (doubleOverlapIso f p W V e)
        (Limits.pullback.diagonal p) (𝟙 Y) (𝟙 Y)
        (Limits.pullback.diagonal_fst p).symm
        (Limits.pullback.diagonal_snd p).symm =
      Iso.refl ((FiniteEtale.pullback (𝟙 Y)).obj W) := by
  intro r X₀ i Y₀ P Q V e
  let D : Scheme.{u} := Limits.pullback p p
  let gD : D ⟶ X := Limits.pullback.fst p p ≫ p
  have hD : IsProper (gD ≫ f) := inferInstance
  have hY : IsProper (p ≫ f) := inferInstance
  have hg : p = Limits.pullback.diagonal p ≫ gD :=
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ p) (Limits.pullback.diagonal_fst p))).trans
        (Category.id_comp p)).symm
  exact (liftedIso_pullback_over (R := R) (X := X) (Y := Y) (Z := D) (T := Y)
    f p gD W V e (Limits.pullback.fst p p) (Limits.pullback.snd p p)
    rfl Limits.pullback.condition.symm (Limits.pullback.diagonal p) p hg
    (𝟙 Y) (𝟙 Y) (Limits.pullback.diagonal_fst p).symm
    (Limits.pullback.diagonal_snd p).symm (Category.id_comp p) (Category.id_comp p)).trans
      (liftedIso_refl (R := R) f p p W V e (𝟙 Y) (Category.id_comp p))

end DoubleOverlap

end AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting
