/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.RepresenterPullback
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianActionPullback

/-!
# The original overlap on the finite étale representer

Full faithfulness transports a specified overlap isomorphism to the
actual pullbacks of the original finite étale representer. The displayed
sheaf-map formula identifies that transported map with the original one.
Reindexing uses the existing sheaf and scheme pullback comparisons.
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

variable {Y Z T : Scheme.{u}}

/-- Reindex a specified original sheaf overlap through the native
inverse-image composition isomorphisms. -/
def reindexSheafIso (F : Sheaf Y.smallEtaleTopology (Type u))
    {a b : Z ⟶ Y}
    (θ : (etaleSetPullback a).obj F ≅ (etaleSetPullback b).obj F)
    (h : T ⟶ Z) (c d : T ⟶ Y) (hc : c = h ≫ a) (hd : d = h ≫ b) :
    (etaleSetPullback c).obj F ≅ (etaleSetPullback d).obj F :=
  eqToIso (congrArg (fun r => (etaleSetPullback r).obj F) hc) ≪≫
    (etaleSetPullbackCompIso h a).app F ≪≫
      (etaleSetPullback h).mapIso θ ≪≫
        ((etaleSetPullbackCompIso h b).app F).symm ≪≫
          eqToIso (congrArg (fun r => (etaleSetPullback r).obj F) hd.symm)

/-- The original sheaf overlap, transported to the actual pullbacks of
its existing finite étale representer. -/
def overlapRepresenterIso
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (a b : Z ⟶ Y)
    (θ : (etaleSetPullback a).obj G.obj ≅ (etaleSetPullback b).obj G.obj) :
    (FiniteEtale.pullback a).obj
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G) ≅
      (FiniteEtale.pullback b).obj
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G) :=
  (finiteEtaleSheafFullyFaithful Z).preimageIso
    ((finiteLocallyConstantPullbackRepresenterIso a G).symm ≪≫ θ ≪≫
      finiteLocallyConstantPullbackRepresenterIso b G)

/-- The transported overlap has exactly the original sheaf map after
the two existing representer comparisons. -/
theorem overlapRepresenterIso_hom
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (a b : Z ⟶ Y)
    (θ : (etaleSetPullback a).obj G.obj ≅ (etaleSetPullback b).obj G.obj) :
    (finiteEtaleSheaf Z).map (overlapRepresenterIso G a b θ).hom =
      (finiteLocallyConstantPullbackRepresenterIso a G).inv ≫ θ.hom ≫
        (finiteLocallyConstantPullbackRepresenterIso b G).hom :=
  (finiteEtaleSheafFullyFaithful Z).map_preimage _

/-- The original overlap square commutes for the actual representer,
with the prescribed original sheaf isomorphism. -/
theorem overlapRepresenterIso_square
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (a b : Z ⟶ Y)
    (θ : (etaleSetPullback a).obj G.obj ≅ (etaleSetPullback b).obj G.obj) :
    (finiteLocallyConstantPullbackRepresenterIso a G).hom ≫
        (finiteEtaleSheaf Z).map (overlapRepresenterIso G a b θ).hom =
      θ.hom ≫ (finiteLocallyConstantPullbackRepresenterIso b G).hom := by
  rw [overlapRepresenterIso_hom, Iso.hom_inv_id_assoc]

/-- The existing representable sheaf composition formula, specialized
to a finite étale cover, uses the native finite-étale comparison. -/
theorem finiteEtaleSheafPullbackIso_comp_hom
    (h : T ⟶ Z) (a : Z ⟶ Y) (W : FiniteEtale Y) :
    ((finiteEtaleSheafPullbackIso (h ≫ a)).app W).hom ≫
        (finiteEtaleSheaf T).map
          ((MorphismProperty.Over.pullbackComp
            (P := @IsFiniteEtale) (Q := ⊤) h a).hom.app W) =
      (etaleSetPullbackCompIso h a).hom.app ((finiteEtaleSheaf Y).obj W) ≫
        (etaleSetPullback h).map ((finiteEtaleSheafPullbackIso a).app W).hom ≫
          ((finiteEtaleSheafPullbackIso h).app ((FiniteEtale.pullback a).obj W)).hom :=
  etaleSetPullbackYonedaObjIso_comp_hom h a ((finiteEtaleToEtale Y).obj W)

/-- The original finite locally constant sheaf has the same composition
comparison as its native scheme representer. -/
theorem finiteLocallyConstantPullbackRepresenterIso_comp_hom
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (h : T ⟶ Z) (a : Z ⟶ Y) :
    (finiteLocallyConstantPullbackRepresenterIso (h ≫ a) G).hom ≫
        (finiteEtaleSheaf T).map
          ((MorphismProperty.Over.pullbackComp
            (P := @IsFiniteEtale) (Q := ⊤) h a).hom.app
              ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)) =
      (etaleSetPullbackCompIso h a).hom.app G.obj ≫
        (etaleSetPullback h).map (finiteLocallyConstantPullbackRepresenterIso a G).hom ≫
          ((finiteEtaleSheafPullbackIso h).app
            ((FiniteEtale.pullback a).obj
              ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G))).hom := by
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
  let α : G.obj ≅ (finiteEtaleSheaf Y).obj W :=
    (((ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := Y))).mapIso
      ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).counitIso.app G)).symm)
  have hn :
      (etaleSetPullback (h ≫ a)).map α.hom ≫
          (etaleSetPullbackCompIso h a).hom.app ((finiteEtaleSheaf Y).obj W) =
        (etaleSetPullbackCompIso h a).hom.app G.obj ≫
          (etaleSetPullback h).map ((etaleSetPullback a).map α.hom) :=
    (etaleSetPullbackCompIso h a).hom.naturality α.hom
  change ((etaleSetPullback (h ≫ a)).map α.hom ≫
      ((finiteEtaleSheafPullbackIso (h ≫ a)).app W).hom) ≫ _ =
    (etaleSetPullbackCompIso h a).hom.app G.obj ≫
      (etaleSetPullback h).map
        ((etaleSetPullback a).map α.hom ≫
          ((finiteEtaleSheafPullbackIso a).app W).hom) ≫ _
  rw [Category.assoc, finiteEtaleSheafPullbackIso_comp_hom, Functor.map_comp]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫
      (etaleSetPullback h).map ((finiteEtaleSheafPullbackIso a).app W).hom ≫
        ((finiteEtaleSheafPullbackIso h).app ((FiniteEtale.pullback a).obj W)).hom) hn)).trans
      (Category.assoc _ _ _)

/-- Reindexing the native representer overlap gives exactly the
reindexed original sheaf overlap, through the original comparisons. -/
theorem overlapRepresenterIso_reindex_square
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (a b : Z ⟶ Y)
    (θ : (etaleSetPullback a).obj G.obj ≅ (etaleSetPullback b).obj G.obj)
    (h : T ⟶ Z) (c d : T ⟶ Y) (hc : c = h ≫ a) (hd : d = h ≫ b) :
    (finiteLocallyConstantPullbackRepresenterIso c G).hom ≫
        (finiteEtaleSheaf T).map
          (FiniteEtale.ProperHenselianActionLifting.reindexIso
            ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)
            (overlapRepresenterIso G a b θ) h c d hc hd).hom =
      (reindexSheafIso G.obj θ h c d hc hd).hom ≫
        (finiteLocallyConstantPullbackRepresenterIso d G).hom := by
  subst c
  subst d
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
  let J := finiteEtaleSheaf T
  let H := etaleSetPullback h
  let K := FiniteEtale.pullback h
  let γ := overlapRepresenterIso G a b θ
  let A := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h a).app W
  let B := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) h b).app W
  let JA := J.mapIso A
  let JB := J.mapIso B
  let ca := finiteLocallyConstantPullbackRepresenterIso a G
  let cb := finiteLocallyConstantPullbackRepresenterIso b G
  let ca' := finiteLocallyConstantPullbackRepresenterIso (h ≫ a) G
  let cb' := finiteLocallyConstantPullbackRepresenterIso (h ≫ b) G
  let Sa := (etaleSetPullbackCompIso h a).app G.obj
  let Sb := (etaleSetPullbackCompIso h b).app G.obj
  let ra := (finiteEtaleSheafPullbackIso h).app ((FiniteEtale.pullback a).obj W)
  let rb := (finiteEtaleSheafPullbackIso h).app ((FiniteEtale.pullback b).obj W)
  have hA : ca'.hom ≫ JA.hom = Sa.hom ≫ H.map ca.hom ≫ ra.hom :=
    finiteLocallyConstantPullbackRepresenterIso_comp_hom G h a
  have hB : cb'.hom ≫ JB.hom = Sb.hom ≫ H.map cb.hom ≫ rb.hom :=
    finiteLocallyConstantPullbackRepresenterIso_comp_hom G h b
  have hn : H.map ((finiteEtaleSheaf Z).map γ.hom) ≫ rb.hom =
      ra.hom ≫ J.map (K.map γ.hom) :=
    (finiteEtaleSheafPullbackIso h).hom.naturality γ.hom
  have hγ : ca.hom ≫ (finiteEtaleSheaf Z).map γ.hom = θ.hom ≫ cb.hom :=
    overlapRepresenterIso_square G a b θ
  have hB' : H.map cb.hom ≫ rb.hom ≫ JB.inv = Sb.inv ≫ cb'.hom := by
    have hb' := congrArg (fun k => Sb.inv ≫ k ≫ JB.inv) hB
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using hb'.symm
  change ca'.hom ≫ J.map ((A.hom ≫ K.map γ.hom) ≫ B.inv) =
    (reindexSheafIso G.obj θ h (h ≫ a) (h ≫ b) rfl rfl).hom ≫ cb'.hom
  have hr :
      (reindexSheafIso G.obj θ h (h ≫ a) (h ≫ b) rfl rfl).hom =
        Sa.hom ≫ H.map θ.hom ≫ Sb.inv := by
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
    (Sa.hom ≫ H.map θ.hom ≫ Sb.inv) ≫ cb'.hom
  calc
    _ = Sa.hom ≫ H.map ca.hom ≫ ra.hom ≫ J.map (K.map γ.hom) ≫ JB.inv := by
      rw [← Category.assoc, ← Category.assoc, hA]
      simp only [Category.assoc]
    _ = Sa.hom ≫ H.map ca.hom ≫
        H.map ((finiteEtaleSheaf Z).map γ.hom) ≫ rb.hom ≫ JB.inv := by
      rw [← Category.assoc ra.hom, ← hn]
      simp only [Category.assoc]
    _ = Sa.hom ≫ H.map θ.hom ≫ H.map cb.hom ≫ rb.hom ≫ JB.inv := by
      rw [← Category.assoc (H.map ca.hom), ← Functor.map_comp, hγ, Functor.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [hB']
      simp only [Category.assoc]

/-- The actual finite étale reindexing and transport of the original
reindexed sheaf isomorphism are equal, by the existing full faithfulness. -/
theorem overlapRepresenterIso_reindex
    (G : EtaleFiniteLocallyConstantSetSheaf Y) (a b : Z ⟶ Y)
    (θ : (etaleSetPullback a).obj G.obj ≅ (etaleSetPullback b).obj G.obj)
    (h : T ⟶ Z) (c d : T ⟶ Y) (hc : c = h ≫ a) (hd : d = h ≫ b) :
    FiniteEtale.ProperHenselianActionLifting.reindexIso
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)
        (overlapRepresenterIso G a b θ) h c d hc hd =
      overlapRepresenterIso G c d (reindexSheafIso G.obj θ h c d hc hd) := by
  apply Iso.ext
  apply (finiteEtaleSheafFullyFaithful T).map_injective
  apply (cancel_epi (finiteLocallyConstantPullbackRepresenterIso c G).hom).mp
  exact (overlapRepresenterIso_reindex_square G a b θ h c d hc hd).trans
    (overlapRepresenterIso_square G c d (reindexSheafIso G.obj θ h c d hc hd)).symm

end EtaleCohomology.SetSheafDescent
