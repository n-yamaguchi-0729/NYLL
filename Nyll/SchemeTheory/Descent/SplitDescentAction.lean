/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.ActionOverlap
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Effective descent along a section for actual geometric actions

The identity and composition equations are the ordinary geometric descent
cocycle on the actual double and triple pullbacks. Given a section of the
base morphism, its pullback of the original cover is an explicit descended
object. The comparison and its inverse are constructed from the original
action. No effectiveness or comparison isomorphism is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.SplitDescentAction

variable {S Y W T : Scheme.{u}} (q : Y ⟶ S) (p : W ⟶ Y)
  (a : pullback q (p ≫ q) ⟶ W)

/-- Apply the specified geometric action to an actual compatible pair. -/
def eval (y : T ⟶ Y) (w : T ⟶ W) (h : y ≫ q = w ≫ p ≫ q) : T ⟶ W :=
  pullback.lift y w h ≫ a

lemma eval_base (ha : a ≫ p = pullback.fst q (p ≫ q))
    (y : T ⟶ Y) (w : T ⟶ W) (h : y ≫ q = w ≫ p ≫ q) :
    eval q p a y w h ≫ p = y := by
  rw [eval, Category.assoc, ha, pullback.lift_fst]

lemma comp_eval {T' : Scheme.{u}} (k : T' ⟶ T)
    (y : T ⟶ Y) (w : T ⟶ W) (h : y ≫ q = w ≫ p ≫ q) :
    k ≫ eval q p a y w h =
      eval q p a (k ≫ y) (k ≫ w)
        (by simpa only [Category.assoc] using congrArg (fun b => k ≫ b) h) := by
  unfold eval
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

lemma eval_roundtrip (ha : a ≫ p = pullback.fst q (p ≫ q))
    (hunit : pullback.lift p (𝟙 W) (Category.id_comp (p ≫ q)).symm ≫ a = 𝟙 W)
    (htrans :
      pullbackActionStep q (p ≫ q) a
          ((Category.assoc a p q).symm.trans (congrArg (fun b => b ≫ q) ha)) ≫ a =
        pullbackSkipMiddle q (p ≫ q) ≫ a)
    (y : T ⟶ Y) (w : T ⟶ W) (h : y ≫ q = w ≫ p ≫ q)
    (hback : (w ≫ p) ≫ q = eval q p a y w h ≫ p ≫ q) :
    eval q p a (w ≫ p) (eval q p a y w h) hback = w := by
  let k := pullback.lift y w h
  have hf : pullbackActionFlip q p a ha ≫ a = pullback.snd q (p ≫ q) := by
    have hsq := congrArg (fun b => b ≫ pullback.snd q (p ≫ q))
      (pullbackActionFlip_sq q p a ha hunit htrans)
    simpa only [Category.assoc, pullbackActionFlip, pullback.lift_snd,
      Category.id_comp] using hsq
  have hk : k ≫ pullbackActionFlip q p a ha =
      pullback.lift (w ≫ p) (eval q p a y w h) hback := by
    apply pullback.hom_ext
    · simp only [k, pullbackActionFlip, Category.assoc, pullback.lift_fst,
        pullback.lift_snd_assoc]
    · simp only [k, pullbackActionFlip, eval, Category.assoc, pullback.lift_snd]
  change _ ≫ a = w
  rw [← hk, Category.assoc, hf]
  exact pullback.lift_snd y w h

section SectionProjection

variable (ha : a ≫ p = pullback.fst q (p ≫ q))
  (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S)

/-- Act on the original cover towards the specified section. -/
def sectionContraction : W ⟶ W :=
  eval q p a (p ≫ q ≫ s) (𝟙 W) (by
    simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])

include ha in
lemma sectionContraction_base : sectionContraction q p a s hs ≫ p = (p ≫ q) ≫ s := by
  exact (eval_base q p a ha _ _ _).trans (Category.assoc p q s).symm

/-- The quotient projection to the section pullback uses the original
contraction, together with the original structure morphism. -/
def sectionProjection : W ⟶ pullback p s :=
  pullback.lift (sectionContraction q p a s hs) (p ≫ q)
    (sectionContraction_base q p a ha s hs)

@[reassoc]
lemma sectionProjection_fst :
    sectionProjection q p a ha s hs ≫ pullback.fst p s = sectionContraction q p a s hs :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma sectionProjection_snd :
    sectionProjection q p a ha s hs ≫ pullback.snd p s = p ≫ q :=
  pullback.lift_snd _ _ _

end SectionProjection

/-- A section supplies an actual descended object: the pullback of the
original object along the section. The displayed isomorphism is built
from the original action and its original identity and triple laws. -/
theorem exists_sectionRestrictionIso
    (ha : a ≫ p = pullback.fst q (p ≫ q))
    (hunit : pullback.lift p (𝟙 W) (Category.id_comp (p ≫ q)).symm ≫ a = 𝟙 W)
    (htrans :
      pullbackActionStep q (p ≫ q) a
          ((Category.assoc a p q).symm.trans (congrArg (fun b => b ≫ q) ha)) ≫ a =
        pullbackSkipMiddle q (p ≫ q) ≫ a)
    (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S) :
    ∃ e : pullback (pullback.snd p s) q ≅ W,
      e.hom ≫ p = pullback.snd (pullback.snd p s) q ∧
        e.inv ≫ pullback.fst (pullback.snd p s) q =
          sectionProjection q p a ha s hs := by
  let V := pullback p s
  let v : V ⟶ S := pullback.snd p s
  let B := pullback v q
  let y : B ⟶ Y := pullback.snd v q
  let w : B ⟶ W := pullback.fst v q ≫ pullback.fst p s
  have hw : w ≫ p = y ≫ q ≫ s := by
    dsimp only [w, y, v]
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
    exact Category.assoc _ _ _
  have he : y ≫ q = w ≫ p ≫ q := by
    rw [← Category.assoc, hw]
    simp only [Category.assoc, hs, Category.comp_id]
  let e : B ⟶ W := eval q p a y w he
  have hep : e ≫ p = y := eval_base q p a ha y w he
  have hh : (p ≫ q ≫ s) ≫ q = (𝟙 W) ≫ p ≫ q := by
    rw [Category.assoc, Category.assoc, hs, Category.comp_id, Category.id_comp]
  let h : W ⟶ W := eval q p a (p ≫ q ≫ s) (𝟙 W) hh
  have hp : h ≫ p = (p ≫ q) ≫ s := by
    exact (eval_base q p a ha (p ≫ q ≫ s) (𝟙 W) hh).trans
      (Category.assoc p q s).symm
  let b₀ : W ⟶ V := sectionProjection q p a ha s hs
  let b : W ⟶ B := pullback.lift b₀ p (pullback.lift_snd _ _ _)
  have bv : b ≫ pullback.fst v q = b₀ := pullback.lift_fst _ _ _
  have hby : b ≫ y = p := pullback.lift_snd _ _ _
  have bw : b ≫ w = h := by
    dsimp only [w]
    rw [← Category.assoc, bv]
    exact pullback.lift_fst _ _ _
  have bh : b ≫ e = 𝟙 W := by
    have he' := comp_eval q p a b y w he
    have hrt := eval_roundtrip q p a ha hunit htrans
      (p ≫ q ≫ s) (𝟙 W) hh
      (by rw [Category.id_comp, ← Category.assoc, hp, Category.assoc, hs,
        Category.comp_id])
    simp only [hby, bw] at he'
    simp only [Category.id_comp] at hrt
    exact he'.trans hrt
  have eh : e ≫ h = w := by
    have hh' := comp_eval q p a e (p ≫ q ≫ s) (𝟙 W) hh
    have hy : e ≫ (p ≫ q ≫ s) = w ≫ p := by
      rw [← Category.assoc, ← Category.assoc, hep, hw]
      exact Category.assoc _ _ _
    have hrt := eval_roundtrip q p a ha hunit htrans y w he
      (by rw [hw, Category.assoc, Category.assoc, hs, Category.comp_id,
        ← Category.assoc, hep])
    simp only [hy, Category.comp_id] at hh'
    exact hh'.trans hrt
  have eb : e ≫ b = 𝟙 B := by
    apply pullback.hom_ext
    · rw [Category.assoc, bv, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, sectionProjection_fst]
        exact eh
      · rw [Category.assoc, sectionProjection_snd, ← Category.assoc, hep]
        exact (pullback.condition (f := v) (g := q)).symm
    · rw [Category.assoc, hby, Category.id_comp]
      exact hep
  exact ⟨⟨e, b, eb, bh⟩, hep, bv⟩

/-- For a finite étale cover with its actual geometric descent action,
the section pullback is a finite étale descended cover, and its original
pullback recovers the specified cover. -/
theorem finiteEtale_section_pullback_recovers
    (V : FiniteEtale Y)
    (aV : pullback q (V.hom ≫ q) ⟶ V.left)
    (haV : aV ≫ V.hom = pullback.fst q (V.hom ≫ q))
    (hunit : pullback.lift V.hom (𝟙 V.left)
      (Category.id_comp (V.hom ≫ q)).symm ≫ aV = 𝟙 V.left)
    (htrans :
      pullbackActionStep q (V.hom ≫ q) aV
          ((Category.assoc aV V.hom q).symm.trans
            (congrArg (fun b => b ≫ q) haV)) ≫ aV =
        pullbackSkipMiddle q (V.hom ≫ q) ≫ aV)
    (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S) :
    Nonempty ((FiniteEtale.pullback q).obj ((FiniteEtale.pullback s).obj V) ≅ V) := by
  obtain ⟨e, he, _⟩ := exists_sectionRestrictionIso q V.hom aV haV hunit htrans s hs
  exact ⟨MorphismProperty.Over.isoMk e he⟩

end AlgebraicGeometry.SplitDescentAction
