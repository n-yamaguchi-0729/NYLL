/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
public import Nyll.EtaleCohomology.Descent.ProperSurjectiveFiniteLocallyConstant
public import Nyll.EtaleCohomology.Descent.SetSheafDescentEqualizer
public import Nyll.EtaleCohomology.Descent.SetSheafDescentProperComparison
public import Nyll.EtaleCohomology.Descent.SetSheafDescentRepresenter
public import Nyll.EtaleCohomology.Descent.SetSheafOverlapCocycle
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleFundamentalGroups.Cohomology.RepresenterPullback
public import Nyll.SchemeTheory.FiniteEtale.RadicialDescentCocycle
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Finite étale representation of the original proper descent sheaf

The original matching comparison is invertible by proper descent. Finite
local constancy therefore descends to the actual matching sheaf, and the
existing finite étale equivalence supplies its representer. Its inverse
image recovers the original sheaf through the original matching counit.

For an original finite étale cover, full faithfulness returns an actual
isomorphism to that same cover. The comparison equation retains the
literal counit and the specified original overlap. Only the original
triple cocycle is required; no effective-descent or local-constancy
conclusion is assumed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.Cohomology

universe u

namespace EtaleCohomology.SetSheafDescent

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [IsProper q] [Surjective q]

/-- A specified compatible isomorphism upstairs identifies the original
sheaf downstairs with the actual matching sheaf. The identification is
unique and recovers the specified isomorphism through the original counit. -/
theorem existsUnique_iso_matchingSheaf
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
    (H : Sheaf X.smallEtaleTopology (Type u))
    (a : (etaleSetPullback q).obj H ≅ G.obj)
    (ha : (etaleSetPullback (pullback.fst q q)).map a.hom ≫ θ.hom =
      (overlapComparison q).hom.app H ≫
        (etaleSetPullback (pullback.snd q q)).map a.hom) :
    ∃! e : H ≅ matchingSheaf q G.obj θ,
      (etaleSetPullback q).map e.hom ≫ comparison q G.obj θ = a.hom := by
  obtain ⟨b, hb, huniq⟩ := existsUnique_lift q G.obj θ a.hom ha
  have hc : IsIso (comparison q G.obj θ) :=
    comparison_isIso_of_proper_surjective q G θ htriple
  have hbc : IsIso ((etaleSetPullback q).map b ≫ comparison q G.obj θ) :=
    hb.symm ▸ a.isIso_hom
  have hpb : IsIso ((etaleSetPullback q).map b) :=
    (isIso_comp_right_iff ((etaleSetPullback q).map b) (comparison q G.obj θ)).mp hbc
  have hbi : IsIso b := etaleSetPullback_isIso_of_surjective q b
  refine ⟨asIso b, hb, ?_⟩
  intro e he
  exact Iso.ext (huniq e.hom he)

/-- The original proper descent sheaf has an actual finite étale
representer. Its original counit recovers the given sheaf and overlap. -/
theorem exists_finiteEtale_representation_of_proper_descent
    (G : EtaleFiniteLocallyConstantSetSheaf Y)
    (θ : (etaleSetPullback (pullback.fst q q)).obj G.obj ≅
      (etaleSetPullback (pullback.snd q q)).obj G.obj)
    (htriple :
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        sheafPairIso q G.obj θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q)) :
    ∃ (Z : FiniteEtale X)
      (e : (finiteEtaleSheaf X).obj Z ≅ matchingSheaf q G.obj θ)
      (a : (etaleSetPullback q).obj ((finiteEtaleSheaf X).obj Z) ≅ G.obj),
      a.hom = (etaleSetPullback q).map e.hom ≫ comparison q G.obj θ ∧
        (etaleSetPullback (pullback.fst q q)).map a.hom ≫ θ.hom =
          (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj Z) ≫
            (etaleSetPullback (pullback.snd q q)).map a.hom := by
  have hcomparison : IsIso (comparison q G.obj θ) :=
    comparison_isIso_of_proper_surjective q G θ htriple
  have hmatching : IsEtaleFiniteLocallyConstantSet (matchingSheaf q G.obj θ) :=
    IsEtaleFiniteLocallyConstantSet.of_surjective_universallyClosed_pullback q
      (G.property.of_iso (asIso (comparison q G.obj θ)).symm)
  let H : EtaleFiniteLocallyConstantSetSheaf X := ⟨matchingSheaf q G.obj θ, hmatching⟩
  let E := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let Z : FiniteEtale X := E.inverse.obj H
  let e : (finiteEtaleSheaf X).obj Z ≅ matchingSheaf q G.obj θ :=
    (representerSheafIso H).symm
  let a : (etaleSetPullback q).obj ((finiteEtaleSheaf X).obj Z) ≅ G.obj :=
    (etaleSetPullback q).mapIso e ≪≫ asIso (comparison q G.obj θ)
  refine ⟨Z, e, a, rfl, ?_⟩
  let L₁ := etaleSetPullback (pullback.fst q q)
  let L₂ := etaleSetPullback (pullback.snd q q)
  let κ := overlapComparison q
  let b := (etaleSetPullback q).map e.hom
  let c := comparison q G.obj θ
  have hn : L₁.map b ≫ κ.hom.app (matchingSheaf q G.obj θ) =
      κ.hom.app ((finiteEtaleSheaf X).obj Z) ≫ L₂.map b :=
    κ.hom.naturality e.hom
  have hc : L₁.map c ≫ θ.hom =
      κ.hom.app (matchingSheaf q G.obj θ) ≫ L₂.map c :=
    comparison_overlap q G.obj θ
  change L₁.map (b ≫ c) ≫ θ.hom =
    κ.hom.app ((finiteEtaleSheaf X).obj Z) ≫ L₂.map (b ≫ c)
  rw [L₁.map_comp, L₂.map_comp, Category.assoc, hc,
    ← Category.assoc (L₁.map b), hn, Category.assoc]

/-- Effective descent for an original finite étale cover, with the
actual cover recovered and the original counit and overlap retained. -/
theorem exists_finiteEtale_descent_of_proper_surjective
    (W : FiniteEtale Y)
    (θ : (etaleSetPullback (pullback.fst q q)).obj ((finiteEtaleSheaf Y).obj W) ≅
      (etaleSetPullback (pullback.snd q q)).obj ((finiteEtaleSheaf Y).obj W))
    (htriple :
      sheafPairIso q ((finiteEtaleSheaf Y).obj W) θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        sheafPairIso q ((finiteEtaleSheaf Y).obj W) θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      sheafPairIso q ((finiteEtaleSheaf Y).obj W) θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q)) :
    ∃ (Z : FiniteEtale X)
      (e : (finiteEtaleSheaf X).obj Z ≅
        matchingSheaf q ((finiteEtaleSheaf Y).obj W) θ)
      (ρ : (FiniteEtale.pullback q).obj Z ≅ W),
      let r := (finiteEtaleSheafPullbackIso q).hom.app Z ≫
        (finiteEtaleSheaf Y).map ρ.hom
      r = (etaleSetPullback q).map e.hom ≫
          (etaleSetPullback q).map (inclusion q ((finiteEtaleSheaf Y).obj W) θ) ≫
            (etaleSetPullbackPushforwardAdjunction q).counit.app
              ((finiteEtaleSheaf Y).obj W) ∧
        (etaleSetPullback (pullback.fst q q)).map r ≫ θ.hom =
          (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj Z) ≫
            (etaleSetPullback (pullback.snd q q)).map r := by
  let G : EtaleFiniteLocallyConstantSetSheaf Y :=
    (finiteEtaleToFiniteLocallyConstantSetSheaf Y).obj W
  obtain ⟨Z, e, a, ha, hθ⟩ :=
    exists_finiteEtale_representation_of_proper_descent q G θ htriple
  let β : (etaleSetPullback q).obj ((finiteEtaleSheaf X).obj Z) ≅
      (finiteEtaleSheaf Y).obj ((FiniteEtale.pullback q).obj Z) :=
    (finiteEtaleSheafPullbackIso q).app Z
  let ρ : (FiniteEtale.pullback q).obj Z ≅ W :=
    (finiteEtaleSheafFullyFaithful Y).preimageIso (β.symm ≪≫ a)
  have hρ : (finiteEtaleSheaf Y).map ρ.hom = β.inv ≫ a.hom :=
    (finiteEtaleSheafFullyFaithful Y).map_preimage (β.inv ≫ a.hom)
  have hr : β.hom ≫ (finiteEtaleSheaf Y).map ρ.hom = a.hom :=
    (congrArg (fun k => β.hom ≫ k) hρ).trans (β.hom_inv_id_assoc a.hom)
  refine ⟨Z, e, ρ, ?_, ?_⟩
  · exact hr.trans ha
  · exact (congrArg
      (fun k => (etaleSetPullback (pullback.fst q q)).map k ≫ θ.hom) hr).trans
      (hθ.trans (congrArg
        (fun k => (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj Z) ≫
          (etaleSetPullback (pullback.snd q q)).map k) hr.symm))

end EtaleCohomology.SetSheafDescent
