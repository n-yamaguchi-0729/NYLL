/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.OverlapPairHom
public import Nyll.SchemeTheory.Descent.SplitDescentAction

/-!
# The geometric action of the original overlap morphism

The overlap map is directed from the first cover coordinate to the second.
The action therefore applies it to `(old point, new point)`. Its unit and
composition laws are consequences of the ordinary diagonal and triple
cocycle of this same overlap map, reusing the original `pairHom` maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

variable {S Y T T' : Scheme.{u}} (q : Y ⟶ S) (V : Over Y)
  (η : (Over.pullback (Limits.pullback.fst q q)).obj V ⟶
    (Over.pullback (Limits.pullback.snd q q)).obj V)

/-- Place the old point and the new cover coordinate in the original
first overlap pullback, in that order. -/
def overlapActionInput (y : T ⟶ Y) (w : T ⟶ V.left)
    (h : y ≫ q = w ≫ V.hom ≫ q) :
    T ⟶ Limits.pullback V.hom (Limits.pullback.fst q q) :=
  Limits.pullback.lift w
    (Limits.pullback.lift (w ≫ V.hom) y (by simpa only [Category.assoc] using h.symm))
    (by rw [Limits.pullback.lift_fst])

@[reassoc]
lemma overlapActionInput_fst (y : T ⟶ Y) (w : T ⟶ V.left)
    (h : y ≫ q = w ≫ V.hom ≫ q) :
    overlapActionInput q V y w h ≫ Limits.pullback.fst V.hom (Limits.pullback.fst q q) = w :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
lemma overlapActionInput_snd (y : T ⟶ Y) (w : T ⟶ V.left)
    (h : y ≫ q = w ≫ V.hom ≫ q) :
    overlapActionInput q V y w h ≫ Limits.pullback.snd V.hom (Limits.pullback.fst q q) =
      Limits.pullback.lift (w ≫ V.hom) y (by simpa only [Category.assoc] using h.symm) :=
  Limits.pullback.lift_snd _ _ _

lemma comp_overlapActionInput (k : T' ⟶ T) (y : T ⟶ Y) (w : T ⟶ V.left)
    (h : y ≫ q = w ≫ V.hom ≫ q) :
    k ≫ overlapActionInput q V y w h =
      overlapActionInput q V (k ≫ y) (k ≫ w)
        (by simpa only [Category.assoc] using congrArg (fun b => k ≫ b) h) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, overlapActionInput_fst, overlapActionInput_fst]
  · rw [Category.assoc, overlapActionInput_snd, overlapActionInput_snd]
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullback.lift_fst]
    · simp only [Category.assoc, Limits.pullback.lift_snd]

/-- The actual scheme action extracted from the original overlap map. -/
def overlapAction : Limits.pullback q (V.hom ≫ q) ⟶ V.left :=
  overlapActionInput q V (Limits.pullback.fst q (V.hom ≫ q))
      (Limits.pullback.snd q (V.hom ≫ q)) Limits.pullback.condition ≫
    η.left ≫ Limits.pullback.fst V.hom (Limits.pullback.snd q q)

/-- The original action lands over the new cover coordinate. -/
lemma overlapAction_base : overlapAction q V η ≫ V.hom = Limits.pullback.fst q (V.hom ≫ q) := by
  have hη : η.left ≫ Limits.pullback.snd V.hom (Limits.pullback.snd q q) =
      Limits.pullback.snd V.hom (Limits.pullback.fst q q) := Over.w η
  rw [overlapAction, Category.assoc, Category.assoc, Limits.pullback.condition,
    ← Category.assoc η.left, hη, overlapActionInput_snd_assoc, Limits.pullback.lift_snd]

/-- Evaluation of the action is evaluation of the original overlap map
at exactly the specified old and new coordinates. -/
lemma eval_overlapAction (y : T ⟶ Y) (w : T ⟶ V.left)
    (h : y ≫ q = w ≫ V.hom ≫ q) :
    SplitDescentAction.eval q V.hom (overlapAction q V η) y w h =
      overlapActionInput q V y w h ≫ η.left ≫
        Limits.pullback.fst V.hom (Limits.pullback.snd q q) := by
  have hk := comp_overlapActionInput q V (Limits.pullback.lift y w h)
    (Limits.pullback.fst q (V.hom ≫ q)) (Limits.pullback.snd q (V.hom ≫ q))
    Limits.pullback.condition
  simp only [Limits.pullback.lift_fst, Limits.pullback.lift_snd] at hk
  rw [SplitDescentAction.eval, overlapAction, ← Category.assoc, hk]

/-- The existing pair map transports an actual lifted point by the
original overlap action, retaining the given base map. -/
lemma lift_pairHom
    (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q)
    (w : T' ⟶ V.left) (t : T' ⟶ T) (hw : w ≫ V.hom = t ≫ a)
    (h : (t ≫ b) ≫ q = w ≫ V.hom ≫ q) :
    Limits.pullback.lift w t hw ≫ (pairHom q V η a b hab).left =
      Limits.pullback.lift
        (SplitDescentAction.eval q V.hom (overlapAction q V η) (t ≫ b) w h) t
        (SplitDescentAction.eval_base q V.hom (overlapAction q V η)
          (overlapAction_base q V η) (t ≫ b) w h) := by
  have hinput : Limits.pullback.lift w t hw ≫ pairLift q V a b hab =
      overlapActionInput q V (t ≫ b) w h := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, pairLift_fst, Limits.pullback.lift_fst, overlapActionInput_fst]
    · rw [Category.assoc, pairLift_snd, Limits.pullback.lift_snd_assoc,
        overlapActionInput_snd]
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst, hw]
      · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd]
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, pairHom_fst, ← Category.assoc, hinput, Limits.pullback.lift_fst,
      eval_overlapAction]
  · rw [Category.assoc, pairHom_snd, Limits.pullback.lift_snd, Limits.pullback.lift_snd]

/-- The ordinary diagonal equation of the original overlap map supplies
the action's actual unit equation. -/
theorem overlapAction_unit
    (hθ : pairHom q V η (𝟙 Y) (𝟙 Y) rfl = 𝟙 _) :
    Limits.pullback.lift V.hom (𝟙 V.left) (Category.id_comp (V.hom ≫ q)).symm ≫
      overlapAction q V η = 𝟙 V.left := by
  have h := lift_pairHom q V η V.hom V.hom rfl (𝟙 V.left) (𝟙 V.left) rfl
    (by simp only [Category.id_comp])
  rw [pairHom_refl_of_diagonal q V η hθ V.hom] at h
  change Limits.pullback.lift (𝟙 V.left) (𝟙 V.left) rfl ≫
    𝟙 (Limits.pullback V.hom V.hom) = _ at h
  rw [Category.comp_id] at h
  have h' := congrArg (fun r => r ≫ Limits.pullback.fst V.hom V.hom) h
  simpa only [Category.id_comp, Category.assoc,
    Limits.pullback.lift_fst, SplitDescentAction.eval] using h'.symm

/-- The cocycle on the original triple pullback gives composition of
actual evaluations of the original overlap action. -/
theorem eval_overlapAction_compose
    (hθ :
      pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q))
    (z y : T ⟶ Y) (w : T ⟶ V.left)
    (hy : y ≫ q = w ≫ V.hom ≫ q) (hz : z ≫ q = y ≫ q)
    (hz' : z ≫ q =
      SplitDescentAction.eval q V.hom (overlapAction q V η) y w hy ≫ V.hom ≫ q) :
    SplitDescentAction.eval q V.hom (overlapAction q V η) z
        (SplitDescentAction.eval q V.hom (overlapAction q V η) y w hy) hz' =
      SplitDescentAction.eval q V.hom (overlapAction q V η) z w (hz.trans hy) := by
  have hab : (w ≫ V.hom) ≫ q = y ≫ q := by
    simpa only [Category.assoc] using hy.symm
  let r : T ⟶ Limits.pullback V.hom (w ≫ V.hom) :=
    Limits.pullback.lift w (𝟙 T) (Category.id_comp (w ≫ V.hom)).symm
  have h₁ := lift_pairHom q V η (w ≫ V.hom) y hab w (𝟙 T)
    (Category.id_comp (w ≫ V.hom)).symm (by simpa only [Category.id_comp] using hy)
  simp only [Category.id_comp] at h₁
  have h₂ := lift_pairHom q V η y z hz.symm
    (SplitDescentAction.eval q V.hom (overlapAction q V η) y w hy) (𝟙 T)
    ((SplitDescentAction.eval_base q V.hom (overlapAction q V η)
      (overlapAction_base q V η) y w hy).trans (Category.id_comp y).symm)
    (by simpa only [Category.id_comp] using hz')
  simp only [Category.id_comp] at h₂
  have h₃ := lift_pairHom q V η (w ≫ V.hom) z (hab.trans hz.symm) w (𝟙 T)
    (Category.id_comp (w ≫ V.hom)).symm
    (by simpa only [Category.id_comp] using hz.trans hy)
  simp only [Category.id_comp] at h₃
  have hc := congrArg (fun k => r ≫ k.left)
    (pairHom_cocycle_of_triple q V η hθ (w ≫ V.hom) y z hab hz.symm)
  change r ≫ ((pairHom q V η (w ≫ V.hom) y hab).left ≫
      (pairHom q V η y z hz.symm).left) =
    r ≫ (pairHom q V η (w ≫ V.hom) z (hab.trans hz.symm)).left at hc
  rw [← Category.assoc, h₁, h₂, h₃] at hc
  have h := congrArg (fun k => k ≫ Limits.pullback.fst V.hom z) hc
  simpa only [Limits.pullback.lift_fst] using h

/-- The action extracted from the original overlap satisfies its actual
threefold action equation. No new action equation is assumed. -/
theorem overlapAction_assoc
    (hθ :
      pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q)) :
    pullbackActionStep q (V.hom ≫ q) (overlapAction q V η)
        ((Category.assoc (overlapAction q V η) V.hom q).symm.trans
          (congrArg (fun b => b ≫ q) (overlapAction_base q V η))) ≫
        overlapAction q V η =
      pullbackSkipMiddle q (V.hom ≫ q) ≫ overlapAction q V η := by
  let A := Limits.pullback q (V.hom ≫ q)
  let B := Limits.pullback q (Limits.pullback.fst q (V.hom ≫ q) ≫ q)
  let z : B ⟶ Y := Limits.pullback.fst q (Limits.pullback.fst q (V.hom ≫ q) ≫ q)
  let t : B ⟶ A := Limits.pullback.snd q (Limits.pullback.fst q (V.hom ≫ q) ≫ q)
  let y : B ⟶ Y := t ≫ Limits.pullback.fst q (V.hom ≫ q)
  let w : B ⟶ V.left := t ≫ Limits.pullback.snd q (V.hom ≫ q)
  have hy : y ≫ q = w ≫ V.hom ≫ q := by
    dsimp only [y, w]
    rw [Category.assoc, Limits.pullback.condition, Category.assoc]
  have hz : z ≫ q = y ≫ q := by
    exact (Limits.pullback.condition (f := q) (g := Limits.pullback.fst q (V.hom ≫ q) ≫ q)).trans
      (Category.assoc t (Limits.pullback.fst q (V.hom ≫ q)) q).symm
  have hm : SplitDescentAction.eval q V.hom (overlapAction q V η) y w hy =
      t ≫ overlapAction q V η := by
    have hl : Limits.pullback.lift y w hy = t := by
      apply Limits.pullback.hom_ext
      · exact Limits.pullback.lift_fst _ _ _
      · exact Limits.pullback.lift_snd _ _ _
    rw [SplitDescentAction.eval, hl]
  have hz' : z ≫ q =
      SplitDescentAction.eval q V.hom (overlapAction q V η) y w hy ≫ V.hom ≫ q := by
    rw [← Category.assoc, SplitDescentAction.eval_base q V.hom
      (overlapAction q V η) (overlapAction_base q V η)]
    exact hz
  have hc := eval_overlapAction_compose q V η hθ z y w hy hz hz'
  simp only [hm] at hc
  exact hc

/-- The original diagonal and triple equations, together with a section
of the base morphism, yield an actual descended object and comparison.
The comparison uses the action extracted from this same overlap map. -/
theorem exists_sectionRestrictionIso_of_overlap
    (hunit : pairHom q V η (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
    (hθ :
      pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q))
    (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S) :
    ∃ e : Limits.pullback (Limits.pullback.snd V.hom s) q ≅ V.left,
      e.hom ≫ V.hom = Limits.pullback.snd (Limits.pullback.snd V.hom s) q ∧
        e.inv ≫ Limits.pullback.fst (Limits.pullback.snd V.hom s) q =
          SplitDescentAction.sectionProjection q V.hom (overlapAction q V η)
            (overlapAction_base q V η) s hs :=
  SplitDescentAction.exists_sectionRestrictionIso q V.hom (overlapAction q V η)
    (overlapAction_base q V η) (overlapAction_unit q V η hunit)
    (overlapAction_assoc q V η hθ) s hs

/-- For a native finite étale cover, the pullback along the section is
a native finite étale descended cover for the original overlap map. -/
theorem finiteEtale_section_pullback_recovers_of_overlap
    (W : FiniteEtale Y)
    (θ : (Over.pullback (Limits.pullback.fst q q)).obj W.toComma ⟶
      (Over.pullback (Limits.pullback.snd q q)).obj W.toComma)
    (hunit : pairHom q W.toComma θ (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
    (hθ :
      pairHom q W.toComma θ (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q W.toComma θ (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q W.toComma θ (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q))
    (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S) :
    Nonempty ((FiniteEtale.pullback q).obj ((FiniteEtale.pullback s).obj W) ≅ W) := by
  obtain ⟨e, he, _⟩ := exists_sectionRestrictionIso_of_overlap q W.toComma θ hunit hθ s hs
  exact ⟨MorphismProperty.Over.isoMk e he⟩

end AlgebraicGeometry.FiniteEtale
