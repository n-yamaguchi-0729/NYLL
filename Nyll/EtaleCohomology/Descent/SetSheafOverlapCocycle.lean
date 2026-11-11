/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafOverlapRepresenter
public import Nyll.EtaleFundamentalGroups.FiniteEtale.OverlapPairHomReindex
public import Nyll.SchemeTheory.Descent.OverlapAction

/-!
# The original sheaf cocycle on its finite étale representer

The canonical inverse-image comparisons reindex the specified original
sheaf overlap to the same pairs used by the scheme action. Full
faithfulness then transfers its diagonal and triple equations to the
actual pair maps, so the split geometric construction applies.
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

variable {X Y T : Scheme.{u}}

private theorem overlapRepresenterIso_trans
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (a b c : T ⟶ Y)
    (θ : (etaleSetPullback a).obj G.obj ≅ (etaleSetPullback b).obj G.obj)
    (ψ : (etaleSetPullback b).obj G.obj ≅ (etaleSetPullback c).obj G.obj) :
    overlapRepresenterIso G a b θ ≪≫ overlapRepresenterIso G b c ψ =
      overlapRepresenterIso G a c (θ ≪≫ ψ) := by
  apply Iso.ext
  apply (finiteEtaleSheafFullyFaithful T).map_injective
  simp only [Iso.trans_hom, Functor.map_comp, overlapRepresenterIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

private theorem overlapRepresenterIso_refl
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (a : T ⟶ Y) :
    overlapRepresenterIso G a a (Iso.refl ((etaleSetPullback a).obj G.obj)) =
      Iso.refl ((FiniteEtale.pullback a).obj
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)) := by
  apply Iso.ext
  apply (finiteEtaleSheafFullyFaithful T).map_injective
  rw [overlapRepresenterIso_hom]
  simp only [Iso.refl_hom, Category.id_comp, Iso.inv_hom_id]
  exact ((finiteEtaleSheaf T).map_id _).symm

variable (q : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology (Type u))
  (θ : (etaleSetPullback (pullback.fst q q)).obj F ≅
    (etaleSetPullback (pullback.snd q q)).obj F)

/-- Reindex the original sheaf overlap along the actual map determined
by a pair of cover coordinates over the base. -/
def sheafPairIso (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q) :
    (etaleSetPullback a).obj F ≅ (etaleSetPullback b).obj F :=
  reindexSheafIso F θ (pullback.lift a b hab) a b
    (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm

variable (G : EtaleFiniteLocallyConstantSetSheaf Y)
  (ϑ : (etaleSetPullback (pullback.fst q q)).obj G.obj ≅
    (etaleSetPullback (pullback.snd q q)).obj G.obj)

/-- The explicit scheme pair map is the transport of this same
reindexed original sheaf isomorphism. -/
theorem pairHom_overlapRepresenter (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q) :
    FiniteEtale.pairHom q
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G).toComma
        (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) ϑ).hom.hom
        a b hab =
      (overlapRepresenterIso G a b (sheafPairIso q G.obj ϑ a b hab)).hom.hom := by
  exact (FiniteEtale.pairHom_eq_reindexIso_hom q
    ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)
    (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) ϑ) a b hab).trans
      (congrArg (fun e => e.hom.hom)
        (overlapRepresenterIso_reindex G (pullback.fst q q) (pullback.snd q q) ϑ
          (pullback.lift a b hab) a b
          (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm))

/-- The original sheaf diagonal gives the actual diagonal of the
representer's scheme pair map. -/
theorem overlapRepresenter_pairHom_diagonal
    (hunit : sheafPairIso q G.obj ϑ (𝟙 Y) (𝟙 Y) rfl =
      Iso.refl ((etaleSetPullback (𝟙 Y)).obj G.obj)) :
    FiniteEtale.pairHom q
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G).toComma
        (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) ϑ).hom.hom
        (𝟙 Y) (𝟙 Y) rfl = 𝟙 _ := by
  exact (pairHom_overlapRepresenter q G ϑ (𝟙 Y) (𝟙 Y) rfl).trans
    (congrArg (fun e => e.hom.hom)
      ((congrArg (overlapRepresenterIso G (𝟙 Y) (𝟙 Y)) hunit).trans
        (overlapRepresenterIso_refl G (𝟙 Y))))

/-- The single original sheaf cocycle on the actual triple fiber
product gives the scheme cocycle used by the original overlap action. -/
theorem overlapRepresenter_pairHom_triple
    (htriple :
      sheafPairIso q G.obj ϑ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        sheafPairIso q G.obj ϑ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      sheafPairIso q G.obj ϑ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q)) :
    let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
    let η := (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) ϑ).hom.hom
    FiniteEtale.pairHom q W.toComma η (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≫
      FiniteEtale.pairHom q W.toComma η (FiniteEtale.radicialTripleSecond q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
    FiniteEtale.pairHom q W.toComma η (FiniteEtale.radicialTripleFirst q)
      (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q) := by
  intro W η
  let a := FiniteEtale.radicialTripleFirst q
  let b := FiniteEtale.radicialTripleSecond q
  let c := FiniteEtale.radicialTripleThird q
  let θab := sheafPairIso q G.obj ϑ a b (FiniteEtale.radicialTriple_first_second q)
  let θbc := sheafPairIso q G.obj ϑ b c (FiniteEtale.radicialTriple_second_third q)
  let θac := sheafPairIso q G.obj ϑ a c (FiniteEtale.radicialTriple_first_third q)
  have ht : overlapRepresenterIso G a b θab ≪≫ overlapRepresenterIso G b c θbc =
      overlapRepresenterIso G a c θac :=
    (overlapRepresenterIso_trans G a b c θab θbc).trans
      (congrArg (overlapRepresenterIso G a c) htriple)
  exact (congrArg₂ (fun f g => f ≫ g)
      (pairHom_overlapRepresenter q G ϑ a b (FiniteEtale.radicialTriple_first_second q))
      (pairHom_overlapRepresenter q G ϑ b c (FiniteEtale.radicialTriple_second_third q))).trans
    ((congrArg (fun e => e.hom.hom) ht).trans
      (pairHom_overlapRepresenter q G ϑ a c
        (FiniteEtale.radicialTriple_first_third q)).symm)

end EtaleCohomology.SetSheafDescent
