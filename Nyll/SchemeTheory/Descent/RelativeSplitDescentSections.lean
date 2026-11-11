/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.SplitDescentQuotient

/-!
# Original action matching after a split base change

The original action extends morphisms into the original cover along a
splitting of a base change. Its existing evaluation and composition laws
give matching and uniqueness, without constructing a new descent action
or a new overlap sheaf on the base change.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.SplitDescentAction

variable {S Y W S' Y' : Scheme.{u}} (q : Y ⟶ S) (p : W ⟶ Y)
  (a : pullback q (p ≫ q) ⟶ W)

/-- Extend a morphism into the original cover by its original action,
along the specified square of base schemes. -/
def relativeExtendSection (q' : Y' ⟶ S') (π : Y' ⟶ Y) (t : S' ⟶ S)
    (hπ : π ≫ q = q' ≫ t) (w : S' ⟶ W) (hw : w ≫ p ≫ q = t) : Y' ⟶ W :=
  eval q p a π (q' ≫ w)
    (hπ.trans ((congrArg (fun k => q' ≫ k) hw).symm.trans
      (Category.assoc q' w (p ≫ q)).symm))

variable (ha : a ≫ p = pullback.fst q (p ≫ q))

include ha in
/-- The extension lies over the specified original cover coordinate. -/
lemma relativeExtendSection_base
    (q' : Y' ⟶ S') (π : Y' ⟶ Y) (t : S' ⟶ S)
    (hπ : π ≫ q = q' ≫ t) (w : S' ⟶ W) (hw : w ≫ p ≫ q = t) :
    relativeExtendSection q p a q' π t hπ w hw ≫ p = π :=
  eval_base q p a ha _ _ _

variable (hunit : pullback.lift p (𝟙 W) (Category.id_comp (p ≫ q)).symm ≫ a = 𝟙 W)

include hunit in
/-- Original action extension restricts to the original morphism. -/
lemma relativeExtendSection_restriction
    (q' : Y' ⟶ S') (π : Y' ⟶ Y) (t : S' ⟶ S)
    (hπ : π ≫ q = q' ≫ t) (s : S' ⟶ Y') (hs : s ≫ q' = 𝟙 S')
    (w : S' ⟶ W) (hw : w ≫ p ≫ q = t) (hwp : w ≫ p = s ≫ π) :
    s ≫ relativeExtendSection q p a q' π t hπ w hw = w := by
  have h₁ := comp_eval q p a s π (q' ≫ w)
    (hπ.trans ((congrArg (fun k => q' ≫ k) hw).symm.trans
      (Category.assoc q' w (p ≫ q)).symm))
  simp only [← Category.assoc, hs, Category.id_comp] at h₁
  have h₂ := comp_eval q p a w p (𝟙 W) (Category.id_comp (p ≫ q)).symm
  simp only [Category.comp_id, hwp] at h₂
  have h₃ : w ≫ eval q p a p (𝟙 W) (Category.id_comp (p ≫ q)).symm = w :=
    (congrArg (fun k => w ≫ k) hunit).trans (Category.comp_id w)
  exact h₁.trans (h₂.symm.trans h₃)

variable (htrans :
    pullbackActionStep q (p ≫ q) a
        ((Category.assoc a p q).symm.trans (congrArg (fun b => b ≫ q) ha)) ≫ a =
      pullbackSkipMiddle q (p ≫ q) ≫ a)

include ha htrans in
/-- The extension matches under the same original action on the
double overlap of the specified base change. -/
lemma relativeExtendSection_matches
    (q' : Y' ⟶ S') (π : Y' ⟶ Y) (t : S' ⟶ S)
    (hπ : π ≫ q = q' ≫ t) (w : S' ⟶ W) (hw : w ≫ p ≫ q = t)
    (h : (pullback.snd q' q' ≫ π) ≫ q =
      (pullback.fst q' q' ≫ relativeExtendSection q p a q' π t hπ w hw) ≫ p ≫ q) :
    eval q p a (pullback.snd q' q' ≫ π)
        (pullback.fst q' q' ≫ relativeExtendSection q p a q' π t hπ w hw) h =
      pullback.snd q' q' ≫ relativeExtendSection q p a q' π t hπ w hw := by
  let y := pullback.fst q' q' ≫ π
  let z := pullback.snd q' q' ≫ π
  let v := pullback.fst q' q' ≫ q' ≫ w
  have hy : y ≫ q = v ≫ p ≫ q := by
    dsimp only [y, v]
    simp only [Category.assoc, hπ, hw]
  have hz : z ≫ q = y ≫ q := by
    dsimp only [y, z]
    simp only [Category.assoc, hπ]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ t) (pullback.condition (f := q') (g := q')).symm).trans
        (Category.assoc _ _ _))
  have h₁ := comp_eval q p a (pullback.fst q' q') π (q' ≫ w)
    (hπ.trans ((congrArg (fun k => q' ≫ k) hw).symm.trans
      (Category.assoc q' w (p ≫ q)).symm))
  have hz' : z ≫ q = eval q p a y v hy ≫ p ≫ q :=
    h.trans (congrArg (fun k => k ≫ p ≫ q) h₁)
  have hc := eval_compose q p a ha htrans z y v hy hz hz'
  have hstart :
      eval q p a z
          (pullback.fst q' q' ≫ relativeExtendSection q p a q' π t hπ w hw) h =
        eval q p a z (eval q p a y v hy) hz' := by
    congr 1
  have h₂ := comp_eval q p a (pullback.snd q' q') π (q' ≫ w)
    (hπ.trans ((congrArg (fun k => q' ≫ k) hw).symm.trans
      (Category.assoc q' w (p ≫ q)).symm))
  have hv : v = pullback.snd q' q' ≫ q' ≫ w :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ w) (pullback.condition (f := q') (g := q'))).trans
        (Category.assoc _ _ _))
  have he :
      eval q p a z v (hz.trans hy) =
        eval q p a z (pullback.snd q' q' ≫ q' ≫ w)
          (by
            dsimp only [z]
            simp only [Category.assoc, hπ, hw]) := by
    congr 1
  exact hstart.trans (hc.trans (he.trans h₂.symm))

/-- Every original-action matching morphism is recovered by applying
the original action to its restriction along the chosen splitting. -/
lemma relativeMatchingSection_eq_extend
    (q' : Y' ⟶ S') (π : Y' ⟶ Y) (t : S' ⟶ S)
    (hπ : π ≫ q = q' ≫ t) (s : S' ⟶ Y') (hs : s ≫ q' = 𝟙 S')
    (u : Y' ⟶ W)
    (h : (pullback.snd q' q' ≫ π) ≫ q =
      (pullback.fst q' q' ≫ u) ≫ p ≫ q)
    (hmatch : eval q p a (pullback.snd q' q' ≫ π) (pullback.fst q' q' ≫ u) h =
      pullback.snd q' q' ≫ u)
    (hw : (s ≫ u) ≫ p ≫ q = t) :
    u = relativeExtendSection q p a q' π t hπ (s ≫ u) hw := by
  let k : Y' ⟶ pullback q' q' :=
    pullback.lift (q' ≫ s) (𝟙 Y')
      (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have h₁ := comp_eval q p a k (pullback.snd q' q' ≫ π)
    (pullback.fst q' q' ≫ u) h
  have h₂ := congrArg (fun r => k ≫ r) hmatch
  rw [h₁] at h₂
  simp only [k, pullback.lift_snd_assoc, pullback.lift_fst_assoc,
    Category.assoc, Category.id_comp] at h₂
  exact h₂.symm

end AlgebraicGeometry.SplitDescentAction
