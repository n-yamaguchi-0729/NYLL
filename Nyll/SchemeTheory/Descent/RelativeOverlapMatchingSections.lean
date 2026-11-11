/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.OverlapAction
public import Nyll.SchemeTheory.Descent.RelativeSplitDescentSections

/-!
# Matching into the original representer after a split base change

The matching equation uses the original overlap morphism and the actual
map from the new double overlap to the original one. Restriction along
the splitting is bijective on these actual morphisms into the original
cover. The original action supplies the inverse.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

variable {S Y S' Y' : Scheme.{u}} (q : Y ⟶ S)
  (q' : Y' ⟶ S') (π : Y' ⟶ Y) (t : S' ⟶ S) (hπ : π ≫ q = q' ≫ t)

include hπ in
/-- The actual two coordinates of the base-changed double overlap
have the same composite to the original base. -/
lemma relativeOverlap_condition :
    (Limits.pullback.fst q' q' ≫ π) ≫ q =
      (Limits.pullback.snd q' q' ≫ π) ≫ q := by
  simp only [Category.assoc, hπ]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ t) (Limits.pullback.condition (f := q') (g := q'))).trans
      (Category.assoc _ _ _))

/-- The specified square induces the actual map between double
overlaps, with the two original cover coordinates. -/
def relativeOverlapMap : Limits.pullback q' q' ⟶ Limits.pullback q q :=
  Limits.pullback.lift (Limits.pullback.fst q' q' ≫ π)
    (Limits.pullback.snd q' q' ≫ π) (relativeOverlap_condition q q' π t hπ)

@[reassoc]
lemma relativeOverlapMap_fst :
    relativeOverlapMap q q' π t hπ ≫ Limits.pullback.fst q q =
      Limits.pullback.fst q' q' ≫ π :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
lemma relativeOverlapMap_snd :
    relativeOverlapMap q q' π t hπ ≫ Limits.pullback.snd q q =
      Limits.pullback.snd q' q' ≫ π :=
  Limits.pullback.lift_snd _ _ _

variable (V : Over Y)
  (η : (Over.pullback (Limits.pullback.fst q q)).obj V ⟶
    (Over.pullback (Limits.pullback.snd q q)).obj V)

include hπ in
/-- The compatibility needed to evaluate the original action on an
actual morphism into the original cover. -/
lemma relativeOverlapSection_compat (u : Over.mk π ⟶ V) :
    (Limits.pullback.snd q' q' ≫ π) ≫ q =
      (Limits.pullback.fst q' q' ≫ u.left) ≫ V.hom ≫ q := by
  have hu : u.left ≫ V.hom = π := u.w
  have hp :
      (Limits.pullback.fst q' q' ≫ u.left) ≫ V.hom =
        Limits.pullback.fst q' q' ≫ π :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => Limits.pullback.fst q' q' ≫ k) hu)
  exact (relativeOverlap_condition q q' π t hπ).symm.trans
    ((congrArg (fun k => k ≫ q) hp).symm.trans (Category.assoc _ _ _))

/-- Evaluating the original action uses the actual map of double
overlaps and the original overlap morphism, retaining the section map
into the original cover. -/
theorem eval_overlapAction_relative_section (u : Over.mk π ⟶ V) :
    SplitDescentAction.eval q V.hom (overlapAction q V η)
        (Limits.pullback.snd q' q' ≫ π) (Limits.pullback.fst q' q' ≫ u.left)
        (relativeOverlapSection_compat q q' π t hπ V u) =
      Limits.pullback.lift (Limits.pullback.fst q' q' ≫ u.left)
          (relativeOverlapMap q q' π t hπ)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => Limits.pullback.fst q' q' ≫ k) u.w).trans
              (relativeOverlapMap_fst q q' π t hπ).symm)) ≫
        η.left ≫ Limits.pullback.fst V.hom (Limits.pullback.snd q q) := by
  rw [eval_overlapAction]
  have hi :
      overlapActionInput q V (Limits.pullback.snd q' q' ≫ π)
          (Limits.pullback.fst q' q' ≫ u.left)
          (relativeOverlapSection_compat q q' π t hπ V u) =
        Limits.pullback.lift (Limits.pullback.fst q' q' ≫ u.left)
          (relativeOverlapMap q q' π t hπ)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => Limits.pullback.fst q' q' ≫ k) u.w).trans
              (relativeOverlapMap_fst q q' π t hπ).symm)) := by
    apply Limits.pullback.hom_ext
    · rw [overlapActionInput_fst, Limits.pullback.lift_fst]
    · rw [overlapActionInput_snd, Limits.pullback.lift_snd]
      apply Limits.pullback.hom_ext
      · rw [Limits.pullback.lift_fst, relativeOverlapMap_fst]
        exact (Category.assoc _ _ _).trans
          (congrArg (fun k => Limits.pullback.fst q' q' ≫ k) u.w)
      · rw [Limits.pullback.lift_snd, relativeOverlapMap_snd]
  exact congrArg (fun k => k ≫ η.left ≫
    Limits.pullback.fst V.hom (Limits.pullback.snd q q)) hi

/-- The literal original-overlap matching equation is equivalent to
matching under the original action. -/
theorem relativeOverlapSection_matching_iff (u : Over.mk π ⟶ V) :
    (Limits.pullback.lift (Limits.pullback.fst q' q' ≫ u.left)
        (relativeOverlapMap q q' π t hπ)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => Limits.pullback.fst q' q' ≫ k) u.w).trans
            (relativeOverlapMap_fst q q' π t hπ).symm)) ≫ η.left =
      Limits.pullback.lift (Limits.pullback.snd q' q' ≫ u.left)
        (relativeOverlapMap q q' π t hπ)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => Limits.pullback.snd q' q' ≫ k) u.w).trans
            (relativeOverlapMap_snd q q' π t hπ).symm))) ↔
      SplitDescentAction.eval q V.hom (overlapAction q V η)
          (Limits.pullback.snd q' q' ≫ π) (Limits.pullback.fst q' q' ≫ u.left)
          (relativeOverlapSection_compat q q' π t hπ V u) =
        Limits.pullback.snd q' q' ≫ u.left := by
  constructor
  · intro he
    have hp := congrArg
      (fun k => k ≫ Limits.pullback.fst V.hom (Limits.pullback.snd q q)) he
    rw [Category.assoc, ← eval_overlapAction_relative_section,
      Limits.pullback.lift_fst] at hp
    exact hp
  · intro he
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, ← eval_overlapAction_relative_section,
        Limits.pullback.lift_fst]
      exact he
    · have hη : η.left ≫ Limits.pullback.snd V.hom (Limits.pullback.snd q q) =
          Limits.pullback.snd V.hom (Limits.pullback.fst q q) := η.w
      rw [Category.assoc, hη, Limits.pullback.lift_snd, Limits.pullback.lift_snd]

/-- The original overlap equation on the base-changed double overlap
has exactly one matching extension of every morphism above the specified
splitting. The displayed map is literal precomposition by that splitting. -/
theorem relativeOverlapSection_restriction_bijOn
    (hunit : pairHom q V η (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
    (htriple :
      pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q))
    (s : S' ⟶ Y') (hs : s ≫ q' = 𝟙 S') :
    Set.BijOn
      (fun u : Over.mk π ⟶ V =>
        (Over.homMk (s ≫ u.left)
          ((Category.assoc _ _ _).trans (congrArg (fun k => s ≫ k) u.w)) :
          Over.mk (s ≫ π) ⟶ V))
      {u | Limits.pullback.lift (Limits.pullback.fst q' q' ≫ u.left)
          (relativeOverlapMap q q' π t hπ)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => Limits.pullback.fst q' q' ≫ k) u.w).trans
              (relativeOverlapMap_fst q q' π t hπ).symm)) ≫ η.left =
        Limits.pullback.lift (Limits.pullback.snd q' q' ≫ u.left)
          (relativeOverlapMap q q' π t hπ)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => Limits.pullback.snd q' q' ≫ k) u.w).trans
              (relativeOverlapMap_snd q q' π t hπ).symm))}
      Set.univ := by
  let a := overlapAction q V η
  have ha := overlapAction_base q V η
  have hact := overlapAction_assoc q V η htriple
  have huact := overlapAction_unit q V η hunit
  let r : (Over.mk π ⟶ V) → (Over.mk (s ≫ π) ⟶ V) := fun u =>
    Over.homMk (s ≫ u.left)
      ((Category.assoc _ _ _).trans (congrArg (fun k => s ≫ k) u.w))
  have hwq (w : Over.mk (s ≫ π) ⟶ V) : w.left ≫ V.hom ≫ q = t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ q) w.w).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => s ≫ k) hπ).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun k => k ≫ t) hs).trans (Category.id_comp t))))))
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro u hu v hv he
    have hmu := (relativeOverlapSection_matching_iff q q' π t hπ V η u).mp hu
    have hmv := (relativeOverlapSection_matching_iff q q' π t hπ V η v).mp hv
    have heu := SplitDescentAction.relativeMatchingSection_eq_extend q V.hom a
      q' π t hπ s hs u.left (relativeOverlapSection_compat q q' π t hπ V u)
      hmu (hwq (r u))
    have hev := SplitDescentAction.relativeMatchingSection_eq_extend q V.hom a
      q' π t hπ s hs v.left (relativeOverlapSection_compat q q' π t hπ V v)
      hmv (hwq (r v))
    have hh : s ≫ u.left = s ≫ v.left := congrArg (fun k => k.left) he
    apply Over.OverMorphism.ext
    refine heu.trans (Eq.trans ?_ hev.symm)
    congr 1
  · intro w _hw
    let u : Over.mk π ⟶ V :=
      Over.homMk
        (SplitDescentAction.relativeExtendSection q V.hom a q' π t hπ w.left (hwq w))
        (SplitDescentAction.relativeExtendSection_base q V.hom a ha q' π t hπ
          w.left (hwq w))
    refine ⟨u, ?_, ?_⟩
    · exact (relativeOverlapSection_matching_iff q q' π t hπ V η u).mpr
        (SplitDescentAction.relativeExtendSection_matches q V.hom a ha hact
          q' π t hπ w.left (hwq w) (relativeOverlapSection_compat q q' π t hπ V u))
    · apply Over.OverMorphism.ext
      exact SplitDescentAction.relativeExtendSection_restriction q V.hom a huact
        q' π t hπ s hs w.left (hwq w) w.w

end AlgebraicGeometry.FiniteEtale
