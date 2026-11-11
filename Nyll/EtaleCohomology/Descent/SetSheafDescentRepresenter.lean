/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentNaturality
public import Nyll.EtaleCohomology.Descent.SetSheafOverlapRepresenter
public import Nyll.EtaleCohomology.Descent.RepresentedOverlapMatchingSections

/-!
# The original matching sheaf and its actual finite étale representer

The existing equivalence counit identifies the original finite locally
constant coefficient sheaf with its representer. Its overlap square is
proved from the transported original overlap. The existing matching
sheaf functor therefore supplies a comparison of the actual equalizers,
retaining their original inclusions and descent counits.
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

/-- The original equivalence counit, with orientation from the given
coefficient sheaf to the sheaf of its actual finite étale representer. -/
def representerSheafIso :
    G.obj ≅ (finiteEtaleSheaf Y).obj
      ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G) :=
  (((ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := Y))).mapIso
    ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).counitIso.app G)).symm)

/-- The original transported overlap, represented through the actual
étale-site pullback comparisons. -/
def representedOriginalOverlap :
    (etaleSetPullback (pullback.fst q q)).obj
        ((finiteEtaleSheaf Y).obj
          ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)) ≅
      (etaleSetPullback (pullback.snd q q)).obj
        ((finiteEtaleSheaf Y).obj
          ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)) :=
  representedOverlapIso q
    ((finiteEtaleToEtale Y).obj
      ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G))
    ((finiteEtaleToEtale (pullback q q)).mapIso
      (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) θ))

/-- The original equivalence counit respects the specified overlap.
This equation is proved from the actual transported map, not supplied
as an extra descent compatibility assumption. -/
theorem representerSheafIso_overlap :
    (etaleSetPullback (pullback.fst q q)).map (representerSheafIso G).hom ≫
        (representedOriginalOverlap q G θ).hom =
      θ.hom ≫ (etaleSetPullback (pullback.snd q q)).map (representerSheafIso G).hom := by
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
  let p₁ := pullback.fst q q
  let p₂ := pullback.snd q q
  let A := (etaleSetPullback p₁).mapIso (representerSheafIso G)
  let B := (etaleSetPullback p₂).mapIso (representerSheafIso G)
  let β₁ := (finiteEtaleSheafPullbackIso p₁).app W
  let β₂ := (finiteEtaleSheafPullbackIso p₂).app W
  let η := overlapRepresenterIso G p₁ p₂ θ
  let k := (finiteEtaleSheaf (pullback q q)).map η.hom
  have hs : (A.hom ≫ β₁.hom) ≫ k = θ.hom ≫ (B.hom ≫ β₂.hom) :=
    overlapRepresenterIso_square G p₁ p₂ θ
  change A.hom ≫ ((β₁.hom ≫ k) ≫ β₂.inv) = θ.hom ≫ B.hom
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ β₂.inv)
      ((Category.assoc _ _ _).symm.trans hs)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun r => θ.hom ≫ r)
            ((Category.assoc _ _ _).trans
              ((congrArg (fun r => B.hom ≫ r) β₂.hom_inv_id).trans
                (Category.comp_id _)))))))

/-- The actual matching equalizer of the given coefficient sheaf is
identified with that of its represented original overlap. -/
def matchingSheafRepresenterIso :
    matchingSheaf q G.obj θ ≅
      matchingSheaf q
        ((finiteEtaleSheaf Y).obj
          ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G))
        (representedOriginalOverlap q G θ) :=
  mapIso (representerSheafIso G) (representerSheafIso_overlap q G θ)

/-- This identification retains the original descent comparison. -/
@[reassoc]
theorem matchingSheafRepresenterIso_comparison :
    (etaleSetPullback q).map (matchingSheafRepresenterIso q G θ).hom ≫
        comparison q
          ((finiteEtaleSheaf Y).obj
            ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G))
          (representedOriginalOverlap q G θ) =
      comparison q G.obj θ ≫ (representerSheafIso G).hom :=
  mapIso_comparison (representerSheafIso G) (representerSheafIso_overlap q G θ)

end EtaleCohomology.SetSheafDescent
