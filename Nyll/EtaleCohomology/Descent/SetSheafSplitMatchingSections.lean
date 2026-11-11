/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Descent.SetSheafDescentRepresenter
import Nyll.EtaleCohomology.Descent.SetSheafSplitDescent
import Nyll.EtaleCohomology.Descent.RepresentedSplitMatchingSections
import Nyll.EtaleCohomology.Descent.GeometricStalkEvaluationSetSections

/-!
# Original finite locally constant matching sections along a splitting

The specified sheaf overlap and its triple cocycle make the actual
inverse-image map along a splitting bijective on matching global sections.
The proof uses the original equivalence counit, its proved overlap square,
and the naturality of the original global-section map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
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

/-- On the original finite locally constant sheaf, the original
inverse-image section map along the specified splitting is bijective
on the sections matching under the specified overlap. Only its original
triple cocycle is required; the diagonal identity follows from it. -/
theorem matching_globalSections_restriction_bijOn
    (htriple :
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        sheafPairIso q G.obj θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q))
    (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X) :
    Set.BijOn (etaleSetPullbackGlobalSectionsMap s G.obj)
      {v | θ.hom.hom.app (op (Scheme.Etale.mk (𝟙 (pullback q q))))
          (etaleSetPullbackGlobalSectionsMap (pullback.fst q q) G.obj v) =
        etaleSetPullbackGlobalSectionsMap (pullback.snd q q) G.obj v}
      Set.univ := by
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
  let V := (finiteEtaleToEtale Y).obj W
  let A := G.obj
  let B := (finiteEtaleSheaf Y).obj W
  let α : A ≅ B := representerSheafIso G
  let ϑ := representedOriginalOverlap q G θ
  let p₁ := pullback.fst q q
  let p₂ := pullback.snd q q
  let ΓY := (sheafSections Y.smallEtaleTopology (Type u)).obj
    (op (Scheme.Etale.mk (𝟙 Y)))
  let ΓX := (sheafSections X.smallEtaleTopology (Type u)).obj
    (op (Scheme.Etale.mk (𝟙 X)))
  let ΓD := (sheafSections (pullback q q).smallEtaleTopology (Type u)).obj
    (op (Scheme.Etale.mk (𝟙 (pullback q q))))
  let E₀ := (ΓY.mapIso α).toEquiv
  let E₁ := (ΓX.mapIso ((etaleSetPullback s).mapIso α)).toEquiv
  let E₂ := (ΓD.mapIso ((etaleSetPullback p₂).mapIso α)).toEquiv
  let θ₀ := θ.hom.hom.app (op (Scheme.Etale.mk (𝟙 (pullback q q))))
  let ϑ₀ := ϑ.hom.hom.app (op (Scheme.Etale.mk (𝟙 (pullback q q))))
  have hnat {Z : Scheme.{u}} (p : Z ⟶ Y) (v : ΓY.obj A) :
      ((etaleSetPullback p).map α.hom).hom.app
          (op (Scheme.Etale.mk (𝟙 Z)))
          (etaleSetPullbackGlobalSectionsMap p A v) =
        etaleSetPullbackGlobalSectionsMap p B (E₀ v) :=
    (ConcreteCategory.congr_hom
      ((etaleSetPullbackGlobalSectionsNatTrans p).naturality α.hom) v).symm
  have hm (v : ΓY.obj A) :
      θ₀ (etaleSetPullbackGlobalSectionsMap p₁ A v) =
          etaleSetPullbackGlobalSectionsMap p₂ A v ↔
        ϑ₀ (etaleSetPullbackGlobalSectionsMap p₁ B (E₀ v)) =
          etaleSetPullbackGlobalSectionsMap p₂ B (E₀ v) := by
    have he := ConcreteCategory.congr_hom
      (congrArg
        (fun k => k.hom.app (op (Scheme.Etale.mk (𝟙 (pullback q q)))))
        (representerSheafIso_overlap q G θ))
      (etaleSetPullbackGlobalSectionsMap p₁ A v)
    have hl :
        E₂ (θ₀ (etaleSetPullbackGlobalSectionsMap p₁ A v)) =
          ϑ₀ (etaleSetPullbackGlobalSectionsMap p₁ B (E₀ v)) :=
      he.symm.trans (congrArg ϑ₀ (hnat p₁ v))
    have hr :
        E₂ (etaleSetPullbackGlobalSectionsMap p₂ A v) =
          etaleSetPullbackGlobalSectionsMap p₂ B (E₀ v) := hnat p₂ v
    constructor
    · intro hv
      exact hl.symm.trans ((congrArg E₂ hv).trans hr)
    · intro hv
      exact E₂.injective (hl.trans (hv.trans hr.symm))
  have hr (v : ΓY.obj A) :
      E₁ (etaleSetPullbackGlobalSectionsMap s A v) =
        etaleSetPullbackGlobalSectionsMap s B (E₀ v) := hnat s v
  have hrepresented := represented_matching_globalSections_restriction_bijOn q V
    ((finiteEtaleToEtale (pullback q q)).mapIso
      (overlapRepresenterIso G p₁ p₂ θ))
    (overlapRepresenter_pairHom_diagonal_of_triple q G θ htriple)
    (overlapRepresenter_pairHom_triple q G θ htriple) s hs
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro v hv w hw he
    apply E₀.injective
    exact hrepresented.injOn ((hm v).mp hv) ((hm w).mp hw)
      ((hr v).symm.trans ((congrArg E₁ he).trans (hr w)))
  · intro z _hz
    obtain ⟨v, hv, hres⟩ := hrepresented.surjOn (Set.mem_univ (E₁ z))
    let w := E₀.symm v
    have he : E₀ w = v := E₀.apply_symm_apply v
    refine ⟨w, (hm w).mpr ?_, ?_⟩
    · exact (congrArg (fun a => ϑ₀
          (etaleSetPullbackGlobalSectionsMap p₁ B a)) he).trans
        (hv.trans
          (congrArg (etaleSetPullbackGlobalSectionsMap p₂ B) he).symm)
    · apply E₁.injective
      exact (hr w).trans
        ((congrArg (etaleSetPullbackGlobalSectionsMap s B) he).trans hres)

end EtaleCohomology.SetSheafDescent
