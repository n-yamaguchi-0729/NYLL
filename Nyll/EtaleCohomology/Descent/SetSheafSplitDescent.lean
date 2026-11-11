/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafOverlapCocycle
public import Nyll.SchemeTheory.Descent.OverlapAction

/-!
# Split descent from the original sheaf cocycle

The original overlap isomorphism and its triple cocycle supply the
diagonal identity: the diagonal is an invertible idempotent. Consequently
the geometric split construction applies without an extra unit
hypothesis and retains its original action projection.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.Cohomology

universe u

namespace EtaleCohomology.SetSheafDescent

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  (G : EtaleFiniteLocallyConstantSetSheaf Y)
  (θ : (etaleSetPullback (pullback.fst q q)).obj G.obj ≅
    (etaleSetPullback (pullback.snd q q)).obj G.obj)
  (htriple :
    sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleSecond q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
    sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
      (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q))

include htriple in
/-- The original triple cocycle already forces the actual scheme
diagonal to be the identity, since its pair map is an isomorphism. -/
theorem overlapRepresenter_pairHom_diagonal_of_triple :
    FiniteEtale.pairHom q
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G).toComma
        (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) θ).hom.hom
        (𝟙 Y) (𝟙 Y) rfl = 𝟙 _ := by
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
  let η := (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) θ).hom.hom
  let δ := overlapRepresenterIso G (𝟙 Y) (𝟙 Y)
    (sheafPairIso q G.obj θ (𝟙 Y) (𝟙 Y) rfl)
  have he : FiniteEtale.pairHom q W.toComma η (𝟙 Y) (𝟙 Y) rfl = δ.hom.hom :=
    pairHom_overlapRepresenter q G θ (𝟙 Y) (𝟙 Y) rfl
  have hc := FiniteEtale.pairHom_cocycle_of_triple q W.toComma η
    (overlapRepresenter_pairHom_triple q G θ htriple)
    (𝟙 Y) (𝟙 Y) (𝟙 Y) rfl rfl
  have hδ₀ : δ.hom.hom ≫ δ.hom.hom = δ.hom.hom :=
    (congrArg₂ (fun f g => f ≫ g) he he).symm.trans (hc.trans he)
  have hδ : δ.hom ≫ δ.hom = δ.hom :=
    MorphismProperty.Comma.Hom.ext' hδ₀
  have hid : δ.hom = 𝟙 _ :=
    (cancel_epi δ.hom).mp (hδ.trans (Category.comp_id δ.hom).symm)
  exact he.trans (congrArg (fun k => k.hom) hid)

include htriple in
/-- The original sheaf cocycle yields a split descended cover with the
literal original action projection as the inverse comparison projection. -/
theorem exists_sectionRestrictionIso_of_sheafCocycle
    (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X) :
    let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
    let η := (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) θ).hom.hom
    ∃ e : pullback (pullback.snd W.hom s) q ≅ W.left,
      e.hom ≫ W.hom = pullback.snd (pullback.snd W.hom s) q ∧
        e.inv ≫ pullback.fst (pullback.snd W.hom s) q =
          SplitDescentAction.sectionProjection q W.hom
            (FiniteEtale.overlapAction q W.toComma η)
            (FiniteEtale.overlapAction_base q W.toComma η) s hs := by
  intro W η
  exact FiniteEtale.exists_sectionRestrictionIso_of_overlap q W.toComma η
    (overlapRepresenter_pairHom_diagonal_of_triple q G θ htriple)
    (overlapRepresenter_pairHom_triple q G θ htriple) s hs

include htriple in
/-- The actual finite étale pullback along the splitting descends the
representer of the original sheaf with its specified cocycle. -/
theorem finiteEtale_section_pullback_recovers_of_sheafCocycle
    (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X) :
    let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
    Nonempty ((FiniteEtale.pullback q).obj ((FiniteEtale.pullback s).obj W) ≅ W) := by
  intro W
  obtain ⟨e, he, _⟩ := exists_sectionRestrictionIso_of_sheafCocycle q G θ htriple s hs
  exact ⟨MorphismProperty.Over.isoMk e he⟩

end EtaleCohomology.SetSheafDescent
