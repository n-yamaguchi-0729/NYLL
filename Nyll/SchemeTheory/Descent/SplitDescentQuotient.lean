/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.SplitDescentAction
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The actual quotient projection for split geometric descent

The projection from a cover with descent action to its pullback along a
section is obtained by acting towards that section. Associativity makes
this projection invariant under the original action. Its literal map,
with its original section, is a coequalizer of the action and projection.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.SplitDescentAction

variable {S Y W T : Scheme.{u}} (q : Y ⟶ S) (p : W ⟶ Y)
  (a : pullback q (p ≫ q) ⟶ W)
  (ha : a ≫ p = pullback.fst q (p ≫ q))
  (htrans :
    pullbackActionStep q (p ≫ q) a
        ((Category.assoc a p q).symm.trans (congrArg (fun b => b ≫ q) ha)) ≫ a =
      pullbackSkipMiddle q (p ≫ q) ≫ a)

include ha htrans in
/-- The original triple equation evaluates to composition on any actual
compatible triple of morphisms. -/
lemma eval_compose
    (z y : T ⟶ Y) (w : T ⟶ W)
    (hy : y ≫ q = w ≫ p ≫ q) (hz : z ≫ q = y ≫ q)
    (hz' : z ≫ q = eval q p a y w hy ≫ p ≫ q) :
    eval q p a z (eval q p a y w hy) hz' =
      eval q p a z w (hz.trans hy) := by
  let k : T ⟶ pullback q (pullback.fst q (p ≫ q) ≫ q) :=
    pullback.lift z (pullback.lift y w hy) (by
      rw [pullback.lift_fst_assoc]
      exact hz)
  have hstep : k ≫ pullbackActionStep q (p ≫ q) a
      ((Category.assoc a p q).symm.trans (congrArg (fun b => b ≫ q) ha)) =
      pullback.lift z (eval q p a y w hy) hz' := by
    apply pullback.hom_ext
    · simp only [k, pullbackActionStep, Category.assoc, pullback.lift_fst]
    · simp only [k, pullbackActionStep, eval, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]
  have hskip : k ≫ pullbackSkipMiddle q (p ≫ q) =
      pullback.lift z w (hz.trans hy) := by
    apply pullback.hom_ext
    · simp only [k, pullbackSkipMiddle, Category.assoc, pullback.lift_fst]
    · simp only [k, pullbackSkipMiddle, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]
  have h := congrArg (fun b => k ≫ b) htrans
  simpa only [← Category.assoc, hstep, hskip, eval] using h

variable (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S)

include ha htrans in
/-- Acting twice towards the section equals acting there directly. -/
lemma sectionContraction_invariant :
    a ≫ sectionContraction q p a s hs =
      pullback.snd q (p ≫ q) ≫ sectionContraction q p a s hs := by
  let y := pullback.fst q (p ≫ q)
  let w := pullback.snd q (p ≫ q)
  let z := w ≫ p ≫ q ≫ s
  have hy : y ≫ q = w ≫ p ≫ q := pullback.condition
  have hz : z ≫ q = y ≫ q := by
    dsimp only [z]
    simp only [Category.assoc, hs, Category.comp_id]
    exact hy.symm
  have harg : a ≫ (p ≫ q ≫ s) = z := by
    rw [← Category.assoc, ← Category.assoc, ha, Category.assoc]
    simpa only [Category.assoc] using congrArg (fun b => b ≫ s) hy
  have hid : eval q p a y w hy = a := by
    have hl : pullback.lift y w hy = 𝟙 (pullback q (p ≫ q)) := by
      apply pullback.hom_ext <;>
        simp only [y, w, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    rw [eval, hl, Category.id_comp]
  have hz' : z ≫ q = eval q p a y w hy ≫ p ≫ q := by
    rw [hid, ← Category.assoc, ha]
    exact hz
  have h := eval_compose q p a ha htrans z y w hy hz hz'
  simp only [hid] at h
  have hleft := comp_eval q p a a (p ≫ q ≫ s) (𝟙 W)
    (by simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have hright := comp_eval q p a w (p ≫ q ≫ s) (𝟙 W)
    (by simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])
  simp only [harg, Category.comp_id] at hleft
  simp only [Category.comp_id] at hright
  exact hleft.trans (h.trans hright.symm)

include htrans in
/-- The original action and the original projection have exactly the
same composite with the section quotient. -/
lemma sectionProjection_invariant :
    a ≫ sectionProjection q p a ha s hs =
      pullback.snd q (p ≫ q) ≫ sectionProjection q p a ha s hs := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sectionProjection_fst]
    exact sectionContraction_invariant q p a ha htrans s hs
  · simp only [Category.assoc, sectionProjection_snd]
    rw [← Category.assoc, ha]
    exact pullback.condition

variable
  (hunit : pullback.lift p (𝟙 W) (Category.id_comp (p ≫ q)).symm ≫ a = 𝟙 W)

include hunit in
/-- The actual first projection of the section pullback is a section of
the quotient projection. -/
lemma sectionProjection_section :
    pullback.fst p s ≫ sectionProjection q p a ha s hs = 𝟙 (pullback p s) := by
  have hbase : pullback.fst p s ≫ (p ≫ q ≫ s) = pullback.fst p s ≫ p := by
    rw [← Category.assoc, pullback.condition, Category.assoc,
      ← Category.assoc s q s, hs, Category.id_comp]
  have hk : pullback.fst p s ≫
      pullback.lift (p ≫ q ≫ s) (𝟙 W)
        (by simp only [Category.assoc, hs, Category.comp_id, Category.id_comp]) =
      pullback.fst p s ≫
        pullback.lift p (𝟙 W) (Category.id_comp (p ≫ q)).symm := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, hbase]
    · simp only [Category.assoc, pullback.lift_snd]
  have hc : pullback.fst p s ≫ sectionContraction q p a s hs = pullback.fst p s := by
    rw [sectionContraction, eval, ← Category.assoc, hk, Category.assoc, hunit,
      Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, sectionProjection_fst, Category.id_comp]
    exact hc
  · rw [Category.assoc, sectionProjection_snd, ← Category.assoc, pullback.condition,
      Category.assoc, hs, Category.comp_id, Category.id_comp]

/-- The actual projection and contraction supply the ordinary split
coequalizer diagram. The universal property is the existing categorical
split-coequalizer theorem. -/
def sectionProjection_splitCoequalizer :
    IsSplitCoequalizer a (pullback.snd q (p ≫ q))
      (sectionProjection q p a ha s hs) where
  rightSection := pullback.fst p s
  leftSection := pullback.lift (p ≫ q ≫ s) (𝟙 W) (by
    simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])
  condition := sectionProjection_invariant q p a ha htrans s hs
  rightSection_π := sectionProjection_section q p a ha s hs hunit
  leftSection_bottom := pullback.lift_snd _ _ _
  leftSection_top := (sectionProjection_fst q p a ha s hs).symm

/-- The section pullback with its original projection is a coequalizer
of the original action and second projection. -/
def sectionProjection_isColimit :
    IsColimit (Cofork.ofπ (sectionProjection q p a ha s hs)
      (sectionProjection_invariant q p a ha htrans s hs)) :=
  (sectionProjection_splitCoequalizer q p a ha htrans s hs hunit).isCoequalizer

include htrans hunit in
/-- The original scheme is the actual pullback of its section quotient.
Both cartesian projections are the original structure map and the
explicit action-invariant quotient projection. -/
theorem sectionProjection_isPullback :
    IsPullback (sectionProjection q p a ha s hs) p (pullback.snd p s) q := by
  obtain ⟨e, he, hd⟩ := exists_sectionRestrictionIso q p a ha hunit htrans s hs
  apply IsPullback.of_iso_pullback ⟨sectionProjection_snd q p a ha s hs⟩ e.symm hd
  have h := congrArg (fun b => e.inv ≫ b) he.symm
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.symm_hom] using h

/-- The cartesian action of the descended section pullback is literally
the original specified action. -/
theorem sectionProjection_recovers_action :
    a = (sectionProjection_isPullback q p a ha htrans s hs hunit).lift
      (pullback.snd q (p ≫ q) ≫ sectionProjection q p a ha s hs)
      (pullback.fst q (p ≫ q)) (by
        rw [Category.assoc, sectionProjection_snd]
        exact (pullback.condition (f := q) (g := p ≫ q)).symm) := by
  apply (sectionProjection_isPullback q p a ha htrans s hs hunit).hom_ext
  · rw [IsPullback.lift_fst]
    exact sectionProjection_invariant q p a ha htrans s hs
  · rw [IsPullback.lift_snd]
    exact ha

end AlgebraicGeometry.SplitDescentAction
