/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Descent.SetSheafOverlapCocycle
import Nyll.SchemeTheory.Descent.OverlapPairHom

/-!
# The original sheaf cocycle on arbitrary compatible coordinates

The actual triple-product equation implies the same equation on every
compatible triple. The proof reuses the existing cartesian pair-map
calculation and the proved original representer comparisons.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.Cohomology

universe u

namespace EtaleCohomology.SetSheafDescent

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y T : Scheme.{u}} (q : Y ⟶ X)
  (G : EtaleFiniteLocallyConstantSetSheaf Y)
  (θ : (etaleSetPullback (pullback.fst q q)).obj G.obj ≅
    (etaleSetPullback (pullback.snd q q)).obj G.obj)

/-- The original sheaf cocycle on the actual triple fiber product
holds on every triple of coordinates over the base. -/
theorem sheafPairIso_cocycle_of_triple
    (htriple :
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        sheafPairIso q G.obj θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q))
    (a b c : T ⟶ Y) (hab : a ≫ q = b ≫ q) (hbc : b ≫ q = c ≫ q) :
    sheafPairIso q G.obj θ a b hab ≪≫ sheafPairIso q G.obj θ b c hbc =
      sheafPairIso q G.obj θ a c (hab.trans hbc) := by
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
  let η := (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) θ).hom.hom
  let θab := sheafPairIso q G.obj θ a b hab
  let θbc := sheafPairIso q G.obj θ b c hbc
  let θac := sheafPairIso q G.obj θ a c (hab.trans hbc)
  let δab := overlapRepresenterIso G a b θab
  let δbc := overlapRepresenterIso G b c θbc
  let δac := overlapRepresenterIso G a c θac
  have hc := FiniteEtale.pairHom_cocycle_of_triple q W.toComma η
    (overlapRepresenter_pairHom_triple q G θ htriple) a b c hab hbc
  have hδ₀ : δab.hom.hom ≫ δbc.hom.hom = δac.hom.hom :=
    (congrArg₂ (fun f g => f ≫ g)
      (pairHom_overlapRepresenter q G θ a b hab)
      (pairHom_overlapRepresenter q G θ b c hbc)).symm.trans
        (hc.trans (pairHom_overlapRepresenter q G θ a c (hab.trans hbc)))
  have hδ : δab.hom ≫ δbc.hom = δac.hom :=
    MorphismProperty.Comma.Hom.ext' hδ₀
  let J := finiteEtaleSheaf T
  have hJ : J.map δab.hom ≫ J.map δbc.hom = J.map δac.hom :=
    (J.map_comp δab.hom δbc.hom).symm.trans (congrArg J.map hδ)
  have hs :
      ((finiteLocallyConstantPullbackRepresenterIso a G).inv ≫ θab.hom ≫
          (finiteLocallyConstantPullbackRepresenterIso b G).hom) ≫
        ((finiteLocallyConstantPullbackRepresenterIso b G).inv ≫ θbc.hom ≫
          (finiteLocallyConstantPullbackRepresenterIso c G).hom) =
      (finiteLocallyConstantPullbackRepresenterIso a G).inv ≫ θac.hom ≫
        (finiteLocallyConstantPullbackRepresenterIso c G).hom :=
    (congrArg₂ (fun f g => f ≫ g)
      (overlapRepresenterIso_hom G a b θab)
      (overlapRepresenterIso_hom G b c θbc)).symm.trans
        (hJ.trans (overlapRepresenterIso_hom G a c θac))
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hs
  apply Iso.ext
  apply (cancel_mono (finiteLocallyConstantPullbackRepresenterIso c G).hom).mp
  apply (cancel_epi (finiteLocallyConstantPullbackRepresenterIso a G).inv).mp
  simpa only [Iso.trans_hom, Category.assoc] using hs

end EtaleCohomology.SetSheafDescent
