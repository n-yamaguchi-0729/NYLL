/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.SplitDescentQuotient

/-!
# Matching sections of the original split descent action

A section above a chosen splitting extends by the original action.
The action cocycle makes this extension match on the actual double
overlap, and every matching section is uniquely recovered by this
formula. These are equations of the original scheme section maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.SplitDescentAction

variable {S Y W : Scheme.{u}} (q : Y ⟶ S) (p : W ⟶ Y)
  (a : pullback q (p ≫ q) ⟶ W)
  (ha : a ≫ p = pullback.fst q (p ≫ q))
  (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S)

/-- Extend an actual section above the splitting by applying the
original action toward each cover coordinate. -/
def extendSection (w : S ⟶ W) (hw : w ≫ p = s) : Y ⟶ W :=
  eval q p a (𝟙 Y) (q ≫ w) (by
    rw [Category.id_comp, Category.assoc, ← Category.assoc w p q, hw, hs,
      Category.comp_id])

include ha in
/-- The extended map is an actual section of the original cover. -/
lemma extendSection_base (w : S ⟶ W) (hw : w ≫ p = s) :
    extendSection q p a s hs w hw ≫ p = 𝟙 Y :=
  eval_base q p a ha _ _ _

variable
  (hunit : pullback.lift p (𝟙 W) (Category.id_comp (p ≫ q)).symm ≫ a = 𝟙 W)

include hunit in
/-- The extension restricts to the same original section above the
splitting; its value is not changed by an arbitrary comparison. -/
lemma extendSection_restriction (w : S ⟶ W) (hw : w ≫ p = s) :
    s ≫ extendSection q p a s hs w hw = w := by
  have h₁ := comp_eval q p a s (𝟙 Y) (q ≫ w)
    (by rw [Category.id_comp, Category.assoc, ← Category.assoc w p q, hw, hs,
      Category.comp_id])
  simp only [Category.comp_id, ← Category.assoc, hs, Category.id_comp] at h₁
  have h₂ := comp_eval q p a w p (𝟙 W) (Category.id_comp (p ≫ q)).symm
  simp only [Category.comp_id, hw] at h₂
  have h₃ : w ≫ eval q p a p (𝟙 W) (Category.id_comp (p ≫ q)).symm = w :=
    (congrArg (fun k => w ≫ k) hunit).trans (Category.comp_id w)
  exact h₁.trans (h₂.symm.trans h₃)

variable
  (htrans :
    pullbackActionStep q (p ≫ q) a
        ((Category.assoc a p q).symm.trans (congrArg (fun b => b ≫ q) ha)) ≫ a =
      pullbackSkipMiddle q (p ≫ q) ≫ a)

include ha htrans in
/-- The extension satisfies the original matching equation on the
actual double overlap, by the original action cocycle. -/
lemma extendSection_matches (w : S ⟶ W) (hw : w ≫ p = s)
    (h : pullback.snd q q ≫ q =
      (pullback.fst q q ≫ extendSection q p a s hs w hw) ≫ p ≫ q) :
    eval q p a (pullback.snd q q)
        (pullback.fst q q ≫ extendSection q p a s hs w hw) h =
      pullback.snd q q ≫ extendSection q p a s hs w hw := by
  let y := pullback.fst q q
  let z := pullback.snd q q
  let v := y ≫ q ≫ w
  have hy : y ≫ q = v ≫ p ≫ q := by
    dsimp only [v]
    rw [Category.assoc, Category.assoc, ← Category.assoc w p q, hw, hs,
      Category.comp_id]
  have hz : z ≫ q = y ≫ q := pullback.condition.symm
  have h₁ := comp_eval q p a y (𝟙 Y) (q ≫ w)
    (by rw [Category.id_comp, Category.assoc, ← Category.assoc w p q, hw, hs,
      Category.comp_id])
  simp only [Category.comp_id] at h₁
  have hz' : z ≫ q = eval q p a y v hy ≫ p ≫ q := by
    exact h.trans (congrArg (fun k => k ≫ p ≫ q) h₁)
  have hc := eval_compose q p a ha htrans z y v hy hz hz'
  have hstart :
      eval q p a z (y ≫ extendSection q p a s hs w hw) h =
        eval q p a z (eval q p a y v hy) hz' := by
    congr 1
  have h₂ := comp_eval q p a z (𝟙 Y) (q ≫ w)
    (by rw [Category.id_comp, Category.assoc, ← Category.assoc w p q, hw, hs,
      Category.comp_id])
  simp only [Category.comp_id] at h₂
  have hv : v = z ≫ q ≫ w := by
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ w) (pullback.condition (f := q) (g := q)))).trans
        (Category.assoc _ _ _)
  have he : eval q p a z v (hz.trans hy) =
      eval q p a z (z ≫ q ≫ w)
        (by rw [Category.assoc, Category.assoc, ← Category.assoc w p q, hw, hs,
          Category.comp_id]) := by
    congr 1
  exact hstart.trans (hc.trans (he.trans h₂.symm))

/-- Every matching section is the actual extension of its restriction
to the chosen splitting. This provides uniqueness without replacing the
section or the matching equation by a separately chosen model. -/
lemma matchingSection_eq_extend
    (u : Y ⟶ W) (hu : u ≫ p = 𝟙 Y)
    (h : pullback.snd q q ≫ q = (pullback.fst q q ≫ u) ≫ p ≫ q)
    (hmatch : eval q p a (pullback.snd q q) (pullback.fst q q ≫ u) h =
      pullback.snd q q ≫ u) :
    u = extendSection q p a s hs (s ≫ u)
      (by rw [Category.assoc, hu, Category.comp_id]) := by
  let k : Y ⟶ pullback q q :=
    pullback.lift (q ≫ s) (𝟙 Y)
      (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have h₁ := comp_eval q p a k (pullback.snd q q) (pullback.fst q q ≫ u) h
  have h₂ := congrArg (fun r => k ≫ r) hmatch
  rw [h₁] at h₂
  simp only [k, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    Category.assoc, Category.id_comp] at h₂
  exact h₂.symm

end AlgebraicGeometry.SplitDescentAction
