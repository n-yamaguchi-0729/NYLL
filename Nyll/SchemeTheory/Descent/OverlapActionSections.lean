/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.OverlapAction
public import Nyll.SchemeTheory.Descent.SplitDescentSections

/-!
# The original overlap equation for scheme sections

Evaluation of the overlap action on the two projections is exactly the
original overlap map applied to the first pulled-back section. Thus the
action matching equation is the actual section equation used by the
represented sheaf equalizer.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

variable {S Y : Scheme.{u}} (q : Y ⟶ S) (V : Over Y)
  (η : (Over.pullback (Limits.pullback.fst q q)).obj V ⟶
    (Over.pullback (Limits.pullback.snd q q)).obj V)
  (u : Y ⟶ V.left) (hu : u ≫ V.hom = 𝟙 Y)
  (h : Limits.pullback.snd q q ≫ q =
    (Limits.pullback.fst q q ≫ u) ≫ V.hom ≫ q)

/-- On an actual section, evaluating the original action on the double
overlap applies the original overlap map to the first pulled-back
section, retaining its literal scheme projection. -/
theorem eval_overlapAction_section :
    SplitDescentAction.eval q V.hom (overlapAction q V η)
        (Limits.pullback.snd q q) (Limits.pullback.fst q q ≫ u) h =
      Limits.pullback.lift (Limits.pullback.fst q q ≫ u)
          (𝟙 (Limits.pullback q q))
          (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp]) ≫
        η.left ≫ Limits.pullback.fst V.hom (Limits.pullback.snd q q) := by
  rw [eval_overlapAction]
  have hi : overlapActionInput q V (Limits.pullback.snd q q)
        (Limits.pullback.fst q q ≫ u) h =
      Limits.pullback.lift (Limits.pullback.fst q q ≫ u)
        (𝟙 (Limits.pullback q q))
        (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp]) := by
    apply Limits.pullback.hom_ext
    · rw [overlapActionInput_fst, Limits.pullback.lift_fst]
    · rw [overlapActionInput_snd, Limits.pullback.lift_snd]
      simp only [Category.assoc, hu, Category.comp_id, Limits.pullback.lift_fst_snd]
  exact congrArg (fun r => r ≫ η.left ≫
    Limits.pullback.fst V.hom (Limits.pullback.snd q q)) hi

/-- Matching under the original action is exactly equality of the two
actual pulled-back scheme sections through the specified overlap map. -/
theorem overlapSection_matching_iff :
    (Limits.pullback.lift (Limits.pullback.fst q q ≫ u)
        (𝟙 (Limits.pullback q q))
        (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp]) ≫ η.left =
      Limits.pullback.lift (Limits.pullback.snd q q ≫ u)
        (𝟙 (Limits.pullback q q))
        (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp])) ↔
      SplitDescentAction.eval q V.hom (overlapAction q V η)
          (Limits.pullback.snd q q) (Limits.pullback.fst q q ≫ u) h =
        Limits.pullback.snd q q ≫ u := by
  constructor
  · intro he
    have hp := congrArg
      (fun r => r ≫ Limits.pullback.fst V.hom (Limits.pullback.snd q q)) he
    rw [Category.assoc, ← eval_overlapAction_section q V η u hu h,
      Limits.pullback.lift_fst] at hp
    exact hp
  · intro he
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, ← eval_overlapAction_section q V η u hu h,
        Limits.pullback.lift_fst]
      exact he
    · have hη : η.left ≫ Limits.pullback.snd V.hom (Limits.pullback.snd q q) =
          Limits.pullback.snd V.hom (Limits.pullback.fst q q) := Over.w η
      rw [Category.assoc, hη, Limits.pullback.lift_snd, Limits.pullback.lift_snd]

omit u hu h in
/-- Restriction of actual matching scheme sections to the given
splitting is bijective. Both its domain equation and its map are the
original overlap and original section maps. -/
theorem overlapSection_restriction_bijOn
    (hunit : pairHom q V η (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
    (htriple :
      pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q))
    (s : S ⟶ Y) (hs : s ≫ q = 𝟙 S) :
    Set.BijOn
      (fun u : Over.mk (𝟙 Y) ⟶ V =>
        (Over.homMk (s ≫ u.left)
          ((Category.assoc s u.left V.hom).trans
            ((congrArg (fun k => s ≫ k) u.w).trans (Category.comp_id s))) :
          Over.mk s ⟶ V))
      {u | Limits.pullback.lift (Limits.pullback.fst q q ≫ u.left)
          (𝟙 (Limits.pullback q q))
          ((Category.assoc _ u.left V.hom).trans
            ((congrArg (fun k => Limits.pullback.fst q q ≫ k) u.w).trans
              ((Category.comp_id _).trans (Category.id_comp _).symm))) ≫ η.left =
        Limits.pullback.lift (Limits.pullback.snd q q ≫ u.left)
          (𝟙 (Limits.pullback q q))
          ((Category.assoc _ u.left V.hom).trans
            ((congrArg (fun k => Limits.pullback.snd q q ≫ k) u.w).trans
              ((Category.comp_id _).trans (Category.id_comp _).symm)))}
      Set.univ := by
  let a := overlapAction q V η
  have ha := overlapAction_base q V η
  have hact := overlapAction_assoc q V η htriple
  have huact := overlapAction_unit q V η hunit
  have hc (v : Over.mk (𝟙 Y) ⟶ V) :
      Limits.pullback.snd q q ≫ q =
        (Limits.pullback.fst q q ≫ v.left) ≫ V.hom ≫ q := by
    have hv : v.left ≫ V.hom = 𝟙 Y := v.w
    have hk : v.left ≫ V.hom ≫ q = q :=
      (Category.assoc v.left V.hom q).symm.trans
        ((congrArg (fun k => k ≫ q) hv).trans (Category.id_comp q))
    exact Limits.pullback.condition.symm.trans
      ((congrArg (fun k => Limits.pullback.fst q q ≫ k) hk).symm.trans
        (Category.assoc (Limits.pullback.fst q q) v.left (V.hom ≫ q)).symm)
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro u hu v hv he
    have hmu := (overlapSection_matching_iff q V η u.left u.w (hc u)).mp hu
    have hmv := (overlapSection_matching_iff q V η v.left v.w (hc v)).mp hv
    have heu := SplitDescentAction.matchingSection_eq_extend q V.hom a s hs
      u.left u.w (hc u) hmu
    have hev := SplitDescentAction.matchingSection_eq_extend q V.hom a s hs
      v.left v.w (hc v) hmv
    have hh : s ≫ u.left = s ≫ v.left := congrArg (fun r => r.left) he
    apply Over.OverMorphism.ext
    refine heu.trans (Eq.trans ?_ hev.symm)
    congr 1
  · intro w _hw
    let u : Over.mk (𝟙 Y) ⟶ V :=
      Over.homMk (SplitDescentAction.extendSection q V.hom a s hs w.left w.w)
        (SplitDescentAction.extendSection_base q V.hom a ha s hs w.left w.w)
    refine ⟨u, ?_, ?_⟩
    · exact (overlapSection_matching_iff q V η u.left u.w (hc u)).mpr
        (SplitDescentAction.extendSection_matches q V.hom a ha s hs hact
          w.left w.w (hc u))
    · apply Over.OverMorphism.ext
      exact SplitDescentAction.extendSection_restriction q V.hom a s hs huact
        w.left w.w

end AlgebraicGeometry.FiniteEtale
