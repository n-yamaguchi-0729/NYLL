/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.ProperFiniteEtaleDescent
public import Nyll.EtaleCohomology.Descent.SetSheafOverlapRepresenter
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianActionPullback
public import Nyll.SchemeTheory.FiniteEtale.DensePullback

/-!
# Proper descent from the original finite étale overlap

The existing representable-sheaf pullback comparison transports the
specified finite étale overlap and its triple cocycle. Proper effective
descent then returns an actual finite étale cover with its comparison to
the original cover, the original matching counit, and the overlap equation.
No replacement representer or effective-descent hypothesis is introduced.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.Cohomology
open AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting

universe u

namespace EtaleCohomology.SetSheafDescent

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y Z T : Scheme.{u}}

/-- The original finite étale overlap, transported using the existing
pullback comparison for the sheaf of that same cover. -/
def finiteEtaleOverlapSheafIso (W : FiniteEtale Y) (a b : Z ⟶ Y)
    (θ : (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W) :
    (etaleSetPullback a).obj ((finiteEtaleSheaf Y).obj W) ≅
      (etaleSetPullback b).obj ((finiteEtaleSheaf Y).obj W) :=
  (finiteEtaleSheafPullbackIso a).app W ≪≫
    (finiteEtaleSheaf Z).mapIso θ ≪≫ ((finiteEtaleSheafPullbackIso b).app W).symm

/-- The comparison square uses the original finite étale morphism. -/
theorem finiteEtaleOverlapSheafIso_square (W : FiniteEtale Y) (a b : Z ⟶ Y)
    (θ : (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W) :
    ((finiteEtaleSheafPullbackIso a).app W).hom ≫ (finiteEtaleSheaf Z).map θ.hom =
      (finiteEtaleOverlapSheafIso W a b θ).hom ≫
        ((finiteEtaleSheafPullbackIso b).app W).hom := by
  simp only [finiteEtaleOverlapSheafIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Composition of native overlap maps is preserved by the actual
representable-sheaf comparison. -/
theorem finiteEtaleOverlapSheafIso_trans (W : FiniteEtale Y) (a b c : Z ⟶ Y)
    (θ : (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W)
    (ψ : (FiniteEtale.pullback b).obj W ≅ (FiniteEtale.pullback c).obj W) :
    finiteEtaleOverlapSheafIso W a b θ ≪≫ finiteEtaleOverlapSheafIso W b c ψ =
      finiteEtaleOverlapSheafIso W a c (θ ≪≫ ψ) := by
  apply Iso.ext
  simp only [finiteEtaleOverlapSheafIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- Native reindexing and sheaf reindexing give the same square under
the existing pullback comparisons. -/
theorem finiteEtaleOverlapSheafIso_reindex_square
    (W : FiniteEtale Y) (a b : Z ⟶ Y)
    (θ : (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W)
    (h : T ⟶ Z) (c d : T ⟶ Y) (hc : c = h ≫ a) (hd : d = h ≫ b) :
    ((finiteEtaleSheafPullbackIso c).app W).hom ≫
        (finiteEtaleSheaf T).map (reindexIso W θ h c d hc hd).hom =
      (reindexSheafIso ((finiteEtaleSheaf Y).obj W)
        (finiteEtaleOverlapSheafIso W a b θ) h c d hc hd).hom ≫
          ((finiteEtaleSheafPullbackIso d).app W).hom := by
  subst c
  subst d
  let J := finiteEtaleSheaf T
  let H := etaleSetPullback h
  let K := FiniteEtale.pullback h
  let γ := θ
  let ψ := finiteEtaleOverlapSheafIso W a b θ
  let A := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h a).app W
  let B := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h b).app W
  let JA := J.mapIso A
  let JB := J.mapIso B
  let ca := (finiteEtaleSheafPullbackIso a).app W
  let cb := (finiteEtaleSheafPullbackIso b).app W
  let ca' := (finiteEtaleSheafPullbackIso (h ≫ a)).app W
  let cb' := (finiteEtaleSheafPullbackIso (h ≫ b)).app W
  let Sa := (etaleSetPullbackCompIso h a).app ((finiteEtaleSheaf Y).obj W)
  let Sb := (etaleSetPullbackCompIso h b).app ((finiteEtaleSheaf Y).obj W)
  let ra := (finiteEtaleSheafPullbackIso h).app ((FiniteEtale.pullback a).obj W)
  let rb := (finiteEtaleSheafPullbackIso h).app ((FiniteEtale.pullback b).obj W)
  have hA : ca'.hom ≫ JA.hom = Sa.hom ≫ H.map ca.hom ≫ ra.hom :=
    finiteEtaleSheafPullbackIso_comp_hom h a W
  have hB : cb'.hom ≫ JB.hom = Sb.hom ≫ H.map cb.hom ≫ rb.hom :=
    finiteEtaleSheafPullbackIso_comp_hom h b W
  have hn : H.map ((finiteEtaleSheaf Z).map γ.hom) ≫ rb.hom =
      ra.hom ≫ J.map (K.map γ.hom) :=
    (finiteEtaleSheafPullbackIso h).hom.naturality γ.hom
  have hγ : ca.hom ≫ (finiteEtaleSheaf Z).map γ.hom = ψ.hom ≫ cb.hom :=
    finiteEtaleOverlapSheafIso_square W a b θ
  have hB' : H.map cb.hom ≫ rb.hom ≫ JB.inv = Sb.inv ≫ cb'.hom := by
    have hb' := congrArg (fun k => Sb.inv ≫ k ≫ JB.inv) hB
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using hb'.symm
  change ca'.hom ≫ J.map ((A.hom ≫ K.map γ.hom) ≫ B.inv) =
    (reindexSheafIso ((finiteEtaleSheaf Y).obj W) ψ h (h ≫ a) (h ≫ b) rfl rfl).hom ≫ cb'.hom
  have hr :
      (reindexSheafIso ((finiteEtaleSheaf Y).obj W) ψ h (h ≫ a) (h ≫ b) rfl rfl).hom =
        Sa.hom ≫ H.map ψ.hom ≫ Sb.inv := by
    simp only [reindexSheafIso, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
      Functor.mapIso_hom, Iso.symm_hom, Category.id_comp, Category.comp_id]
    rfl
  have hm : J.map ((A.hom ≫ K.map γ.hom) ≫ B.inv) =
      (JA.hom ≫ J.map (K.map γ.hom)) ≫ JB.inv :=
    (J.map_comp (A.hom ≫ K.map γ.hom) B.inv).trans
      (congrArg (fun k => k ≫ JB.inv) (J.map_comp A.hom (K.map γ.hom)))
  refine (congrArg (fun k => ca'.hom ≫ k) hm).trans ?_
  rw [hr]
  change ca'.hom ≫ (JA.hom ≫ J.map (K.map γ.hom)) ≫ JB.inv =
    (Sa.hom ≫ H.map ψ.hom ≫ Sb.inv) ≫ cb'.hom
  calc
    _ = Sa.hom ≫ H.map ca.hom ≫ ra.hom ≫ J.map (K.map γ.hom) ≫ JB.inv := by
      rw [← Category.assoc, ← Category.assoc, hA]
      simp only [Category.assoc]
    _ = Sa.hom ≫ H.map ca.hom ≫
        H.map ((finiteEtaleSheaf Z).map γ.hom) ≫ rb.hom ≫ JB.inv := by
      rw [← Category.assoc ra.hom, ← hn]
      simp only [Category.assoc]
    _ = Sa.hom ≫ H.map ψ.hom ≫ H.map cb.hom ≫ rb.hom ≫ JB.inv := by
      rw [← Category.assoc (H.map ca.hom), ← Functor.map_comp, hγ, Functor.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [hB']
      simp only [Category.assoc]

/-- The transported native reindexing is the actual reindexed sheaf
isomorphism, with both endpoint comparisons retained. -/
theorem finiteEtaleOverlapSheafIso_reindex
    (W : FiniteEtale Y) (a b : Z ⟶ Y)
    (θ : (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W)
    (h : T ⟶ Z) (c d : T ⟶ Y) (hc : c = h ≫ a) (hd : d = h ≫ b) :
    finiteEtaleOverlapSheafIso W c d (reindexIso W θ h c d hc hd) =
      reindexSheafIso ((finiteEtaleSheaf Y).obj W)
        (finiteEtaleOverlapSheafIso W a b θ) h c d hc hd := by
  apply Iso.ext
  apply (cancel_mono ((finiteEtaleSheafPullbackIso d).app W).hom).mp
  exact (finiteEtaleOverlapSheafIso_square W c d (reindexIso W θ h c d hc hd)).symm.trans
    (finiteEtaleOverlapSheafIso_reindex_square W a b θ h c d hc hd)

/-- Reindex the original native overlap at a pair of cover coordinates. -/
def finiteEtalePairIso (q : Y ⟶ X) (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q) :
    (FiniteEtale.pullback a).obj W ≅ (FiniteEtale.pullback b).obj W :=
  reindexIso W θ (pullback.lift a b hab) a b
    (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm

/-- Native pair maps transport to the original sheaf pair maps. -/
theorem finiteEtaleOverlapSheafIso_pair (q : Y ⟶ X) (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q) :
    finiteEtaleOverlapSheafIso W a b (finiteEtalePairIso q W θ a b hab) =
      sheafPairIso q ((finiteEtaleSheaf Y).obj W)
        (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ) a b hab :=
  finiteEtaleOverlapSheafIso_reindex W (pullback.fst q q) (pullback.snd q q) θ
    (pullback.lift a b hab) a b
    (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm

/-- The original native triple cocycle gives the actual sheaf triple
cocycle used by proper effective descent. -/
theorem finiteEtaleOverlapSheafIso_triple (q : Y ⟶ X) (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (htriple :
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        finiteEtalePairIso q W θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q)) :
    let ψ := finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ
    sheafPairIso q ((finiteEtaleSheaf Y).obj W) ψ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
      sheafPairIso q ((finiteEtaleSheaf Y).obj W) ψ (FiniteEtale.radicialTripleSecond q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
    sheafPairIso q ((finiteEtaleSheaf Y).obj W) ψ (FiniteEtale.radicialTripleFirst q)
      (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q) := by
  dsimp only
  rw [← finiteEtaleOverlapSheafIso_pair, ← finiteEtaleOverlapSheafIso_pair,
    ← finiteEtaleOverlapSheafIso_pair, finiteEtaleOverlapSheafIso_trans, htriple]

/-- Proper effective descent applied to the original native finite étale
cocycle, retaining the original cover, matching counit, and overlap. -/
theorem exists_finiteEtale_descent_of_proper_surjective_native
    (q : Y ⟶ X) [IsProper q] [Surjective q] (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (htriple :
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        finiteEtalePairIso q W θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q)) :
    let ψ := finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ
    ∃ (V : FiniteEtale X)
      (e : (finiteEtaleSheaf X).obj V ≅ matchingSheaf q ((finiteEtaleSheaf Y).obj W) ψ)
      (ρ : (FiniteEtale.pullback q).obj V ≅ W),
      let r := (finiteEtaleSheafPullbackIso q).hom.app V ≫
        (finiteEtaleSheaf Y).map ρ.hom
      r = (etaleSetPullback q).map e.hom ≫
          (etaleSetPullback q).map (inclusion q ((finiteEtaleSheaf Y).obj W) ψ) ≫
            (etaleSetPullbackPushforwardAdjunction q).counit.app
              ((finiteEtaleSheaf Y).obj W) ∧
        (etaleSetPullback (pullback.fst q q)).map r ≫ ψ.hom =
          (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj V) ≫
            (etaleSetPullback (pullback.snd q q)).map r :=
  exists_finiteEtale_descent_of_proper_surjective q W
    (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ)
    (finiteEtaleOverlapSheafIso_triple q W θ htriple)

/-- Two actual covers descending the same native datum are uniquely
isomorphic through an isomorphism preserving their specified comparisons. -/
theorem existsUnique_finiteEtale_iso_of_descent
    (q : Y ⟶ X) [IsProper q] [Surjective q] (W : FiniteEtale Y)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (htriple :
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        finiteEtalePairIso q W θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q))
    (V₁ V₂ : FiniteEtale X)
    (ρ₁ : (FiniteEtale.pullback q).obj V₁ ≅ W)
    (ρ₂ : (FiniteEtale.pullback q).obj V₂ ≅ W)
    (h₁ :
      let r := ((finiteEtaleSheafPullbackIso q).app V₁).hom ≫
        (finiteEtaleSheaf Y).map ρ₁.hom
      (etaleSetPullback (pullback.fst q q)).map r ≫
          (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ).hom =
        (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj V₁) ≫
          (etaleSetPullback (pullback.snd q q)).map r)
    (h₂ :
      let r := ((finiteEtaleSheafPullbackIso q).app V₂).hom ≫
        (finiteEtaleSheaf Y).map ρ₂.hom
      (etaleSetPullback (pullback.fst q q)).map r ≫
          (finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ).hom =
        (overlapComparison q).hom.app ((finiteEtaleSheaf X).obj V₂) ≫
          (etaleSetPullback (pullback.snd q q)).map r) :
    ∃! τ : V₁ ≅ V₂, (FiniteEtale.pullback q).map τ.hom ≫ ρ₂.hom = ρ₁.hom := by
  let G := (finiteEtaleToFiniteLocallyConstantSetSheaf Y).obj W
  let ψ := finiteEtaleOverlapSheafIso W (pullback.fst q q) (pullback.snd q q) θ
  have ht := finiteEtaleOverlapSheafIso_triple q W θ htriple
  let β₁ := (finiteEtaleSheafPullbackIso q).app V₁
  let β₂ := (finiteEtaleSheafPullbackIso q).app V₂
  let a₁ := β₁ ≪≫ (finiteEtaleSheaf Y).mapIso ρ₁
  let a₂ := β₂ ≪≫ (finiteEtaleSheaf Y).mapIso ρ₂
  obtain ⟨e₁, he₁, _⟩ := existsUnique_iso_matchingSheaf q G ψ ht
    ((finiteEtaleSheaf X).obj V₁) a₁ h₁
  obtain ⟨e₂, he₂, _⟩ := existsUnique_iso_matchingSheaf q G ψ ht
    ((finiteEtaleSheaf X).obj V₂) a₂ h₂
  let J := finiteEtaleSheaf X
  let L := etaleSetPullback q
  let c := comparison q G.obj ψ
  let τ : V₁ ≅ V₂ := (finiteEtaleSheafFullyFaithful X).preimageIso (e₁ ≪≫ e₂.symm)
  have hτ : J.map τ.hom = e₁.hom ≫ e₂.inv :=
    (finiteEtaleSheafFullyFaithful X).map_preimage _
  have hc₂ : L.map e₂.inv ≫ a₂.hom = c :=
    (congrArg (fun k => L.map e₂.inv ≫ k) he₂.symm).trans
      ((L.mapIso e₂).inv_hom_id_assoc c)
  have hτa : L.map (J.map τ.hom) ≫ a₂.hom = a₁.hom := by
    rw [hτ, L.map_comp, Category.assoc, hc₂]
    exact he₁
  have hn : L.map (J.map τ.hom) ≫ β₂.hom =
      β₁.hom ≫ (finiteEtaleSheaf Y).map ((FiniteEtale.pullback q).map τ.hom) :=
    (finiteEtaleSheafPullbackIso q).hom.naturality τ.hom
  have hcomp : (FiniteEtale.pullback q).map τ.hom ≫ ρ₂.hom = ρ₁.hom := by
    apply (finiteEtaleSheafFullyFaithful Y).map_injective
    apply (cancel_epi β₁.hom).mp
    rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
    exact hτa
  have hfaithful : (FiniteEtale.pullback q).Faithful :=
    FiniteEtale.pullback_faithful_of_isDominant q
  refine ⟨τ, hcomp, ?_⟩
  intro σ hσ
  apply Iso.ext
  apply (FiniteEtale.pullback q).map_injective
  exact (cancel_mono ρ₂.hom).mp (hσ.trans hcomp.symm)

end EtaleCohomology.SetSheafDescent
