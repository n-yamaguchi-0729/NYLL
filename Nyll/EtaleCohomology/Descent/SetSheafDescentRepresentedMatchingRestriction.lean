/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentMatchingStalk
public import Nyll.EtaleCohomology.Descent.SetSheafDescentRepresentedStalkMatching
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberComponent
public import Nyll.SchemeTheory.Descent.RelativeOverlapMatchingRestrictionAt

public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberProper
public import Nyll.EtaleCohomology.Descent.RepresentedFiberStalkComponent
public import Nyll.EtaleCohomology.Descent.RepresentedOverlapFiberMatching
public import Nyll.EtaleCohomology.Descent.RepresentedOverlapMatchingSections
public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Mathlib.Data.Set.Function

/-!
# Actual matching stalks restrict bijectively to every geometric lift

The original matching-stalk inclusion, the original represented
geometric-fiber section map, and literal restriction at the specified
geometric lift have bijective composite. Properness and the original
finite étale coefficient supply the section comparison, and the original
overlap unit and cocycle supply the split matching extension.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology.SetSheafDescent

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [IsProper q]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (CommRingCat.of Ω) ⟶ X)
  (V : FiniteEtale Y)
  (η : (etaleBaseChange (pullback.fst q q)).obj ((finiteEtaleToEtale Y).obj V) ≅
    (etaleBaseChange (pullback.snd q q)).obj ((finiteEtaleToEtale Y).obj V))
  (hunit : FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
      ((Scheme.Etale.forget (pullback q q)).map η.hom) (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
  (htriple :
    FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
        ((Scheme.Etale.forget (pullback q q)).map η.hom)
        (FiniteEtale.radicialTripleFirst q) (FiniteEtale.radicialTripleSecond q)
        (FiniteEtale.radicialTriple_first_second q) ≫
      FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
        ((Scheme.Etale.forget (pullback q q)).map η.hom)
        (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTripleThird q)
        (FiniteEtale.radicialTriple_second_third q) =
      FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
        ((Scheme.Etale.forget (pullback q q)).map η.hom)
        (FiniteEtale.radicialTripleFirst q) (FiniteEtale.radicialTripleThird q)
        (FiniteEtale.radicialTriple_first_third q))
  (y : Spec (CommRingCat.of Ω) ⟶ Y) (hy : y ≫ q = t)

include hunit htriple in
/-- The actual matching stalk maps bijectively to sections of the
original finite étale cover over the specified geometric lift. -/
theorem represented_matchingStalk_restriction_bijective :
    Function.Bijective
      ((Scheme.pointSmallEtale t).sheafFiber.map
          (inclusion q ((finiteEtaleSheaf Y).obj V)
            (representedOverlapIso q ((finiteEtaleToEtale Y).obj V) η)) ≫
        etaleSetPushforwardRepresentableFiberSections q t
          ((finiteEtaleToEtale Y).obj V) ≫
        representedGeometricFiberRestriction q t
          y hy ((finiteEtaleToEtale Y).obj V)) := by
  let Φ := Scheme.pointSmallEtale t
  let W := (finiteEtaleToEtale Y).obj V
  let F := (finiteEtaleSheaf Y).obj V
  let θ := representedOverlapIso q W η
  let i := Φ.sheafFiber.map (inclusion q F θ)
  let c := etaleSetPushforwardRepresentableFiberSections q t W
  let r := representedGeometricFiberRestriction q t y hy W
  let M : Set (Φ.sheafFiber.obj ((etaleSetPushforward q).obj F)) :=
    {a | Φ.sheafFiber.map (firstArrow q F) a = Φ.sheafFiber.map (secondArrow q F θ) a}
  let P : Set (Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W) :=
    {a | pullback.lift
        (pullback.fst (pullback.fst t q) (pullback.fst t q) ≫ a.left)
        (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
          (pullback.condition (f := t) (g := q)).symm)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => pullback.fst (pullback.fst t q) (pullback.fst t q) ≫ k)
            a.w).trans
              (FiniteEtale.relativeOverlapMap_fst q (pullback.fst t q) (pullback.snd t q) t
                (pullback.condition (f := t) (g := q)).symm).symm)) ≫ η.hom.left =
      pullback.lift
        (pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ a.left)
        (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
          (pullback.condition (f := t) (g := q)).symm)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ k)
            a.w).trans
              (FiniteEtale.relativeOverlapMap_snd q (pullback.fst t q) (pullback.snd t q) t
                (pullback.condition (f := t) (g := q)).symm).symm))}
  let e := matchingSheafStalkIso q F θ Φ
  have he (b : Φ.sheafFiber.obj (matchingSheaf q F θ)) : (e.hom b).val = i b := by
    simpa only [types_comp_apply, TypeCat.ofHom_apply] using
      types_congr_hom (matchingSheafStalkIso_hom_val q F θ Φ) b
  have hi : Set.BijOn i Set.univ M := by
    refine ⟨?_, ?_, ?_⟩
    · intro b _
      exact (he b) ▸ (e.hom b).property
    · intro b _ b' _ hb
      apply e.toEquiv.injective
      apply Subtype.ext
      exact (he b).trans (hb.trans (he b').symm)
    · intro a ha
      obtain ⟨b, hb⟩ := e.toEquiv.surjective ⟨a, ha⟩
      exact ⟨b, Set.mem_univ _, (he b).symm.trans (congrArg Subtype.val hb)⟩
  have hc : Function.Bijective c :=
    etaleSetPushforwardRepresentableFiberSections_bijective q t V
  have hm (a : Φ.sheafFiber.obj ((etaleSetPushforward q).obj F)) : a ∈ M ↔ c a ∈ P :=
    (represented_stalk_matching_iff q t V η a).trans
      (representedSourcePullback_overlap_matching_iff q t W η.hom (c a))
  have hC : Set.BijOn c M P := by
    refine ⟨fun a ha => (hm a).mp ha, fun a _ b _ h => hc.1 h, ?_⟩
    intro u hu
    obtain ⟨a, ha⟩ := hc.2 u
    exact ⟨a, (hm a).mpr (ha.symm ▸ hu), ha⟩
  let σ : Spec (CommRingCat.of Ω) ⟶ pullback t q :=
    pullback.lift (𝟙 _) y ((Category.id_comp t).trans hy.symm)
  have hσ₁ : σ ≫ pullback.fst t q = 𝟙 _ := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ pullback.snd t q = y := pullback.lift_snd _ _ _
  have hR : Set.BijOn r P Set.univ :=
    FiniteEtale.relativeOverlapSection_restriction_bijOn_at q (pullback.fst t q)
      (pullback.snd t q) t (pullback.condition (f := t) (g := q)).symm
      ((FiniteEtale.forget Y).obj V)
      ((Scheme.Etale.forget (pullback q q)).map η.hom) hunit htriple σ hσ₁ y hσ₂
  exact Set.bijOn_univ.mp (hR.comp (hC.comp hi))

end EtaleCohomology.SetSheafDescent
