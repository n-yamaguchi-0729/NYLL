/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Descent.RepresentedOverlapMatchingSections
import Nyll.SchemeTheory.Descent.OverlapActionSections

/-!
# The original H⁰ matching restriction for a split morphism

Restriction of the actual global sections that match under the specified
overlap to a chosen splitting is bijective. The restriction map is the
original inverse-image unit map on H⁰. The proof transports the actual
scheme section construction through the existing represented-section
equivalence, retaining the original maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology.SetSheafDescent

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (W : Y.Etale)
  (η : (etaleBaseChange (pullback.fst q q)).obj W ≅
    (etaleBaseChange (pullback.snd q q)).obj W)

/-- The actual H⁰ inverse-image map along the splitting is bijective
on the original matching sections of the represented sheaf. -/
theorem represented_matching_globalSections_restriction_bijOn
    (hunit : FiniteEtale.pairHom q ((Scheme.Etale.forget Y).obj W) η.hom.hom
      (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
    (htriple :
      FiniteEtale.pairHom q ((Scheme.Etale.forget Y).obj W) η.hom.hom
          (FiniteEtale.radicialTripleFirst q) (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTriple_first_second q) ≫
        FiniteEtale.pairHom q ((Scheme.Etale.forget Y).obj W) η.hom.hom
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTripleThird q)
          (FiniteEtale.radicialTriple_second_third q) =
      FiniteEtale.pairHom q ((Scheme.Etale.forget Y).obj W) η.hom.hom
        (FiniteEtale.radicialTripleFirst q) (FiniteEtale.radicialTripleThird q)
        (FiniteEtale.radicialTriple_first_third q))
    (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X) :
    Set.BijOn
      (etaleSetPullbackGlobalSectionsMap s (Y.smallEtaleTopology.yoneda.obj W))
      {u | (representedOverlapIso q W η).hom.hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback q q))))
          (etaleSetPullbackGlobalSectionsMap (pullback.fst q q)
            (Y.smallEtaleTopology.yoneda.obj W) u) =
        etaleSetPullbackGlobalSectionsMap (pullback.snd q q)
          (Y.smallEtaleTopology.yoneda.obj W) u}
      Set.univ := by
  let V := (Scheme.Etale.forget Y).obj W
  let E := etaleRepresentablePullbackSectionsEquiv s W
  have hscheme := FiniteEtale.overlapSection_restriction_bijOn q V η.hom.hom
    hunit htriple s hs
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro u hu v hv he
    let u₀ : Over.mk (𝟙 Y) ⟶ V := Over.homMk u.left u.w
    let v₀ : Over.mk (𝟙 Y) ⟶ V := Over.homMk v.left v.w
    have hu₀ := (represented_globalSections_matching_iff q W η u).mp hu
    have hv₀ := (represented_globalSections_matching_iff q W η v).mp hv
    have hrestriction :
        (Over.homMk (s ≫ u₀.left)
          ((Category.assoc s u₀.left V.hom).trans
            ((congrArg (fun k => s ≫ k) u₀.w).trans (Category.comp_id s))) :
          Over.mk s ⟶ V) =
        Over.homMk (s ≫ v₀.left)
          ((Category.assoc s v₀.left V.hom).trans
            ((congrArg (fun k => s ≫ k) v₀.w).trans (Category.comp_id s))) := by
      apply E.injective
      exact (etaleSetPullbackGlobalSectionsMap_eq_representableSectionsEquiv s W u).symm.trans
        (he.trans (etaleSetPullbackGlobalSectionsMap_eq_representableSectionsEquiv s W v))
    have huv : u₀ = v₀ := hscheme.injOn hu₀ hv₀ hrestriction
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun r => r.left) huv
  · intro z _hz
    let w : Over.mk s ⟶ V := E.symm z
    obtain ⟨u, hu, hres⟩ := hscheme.surjOn (Set.mem_univ w)
    let u' : (Scheme.Etale.mk (𝟙 Y) : Y.Etale) ⟶ W :=
      MorphismProperty.Over.homMk u.left u.w
    refine ⟨u', (represented_globalSections_matching_iff q W η u').mpr hu, ?_⟩
    exact (etaleSetPullbackGlobalSectionsMap_eq_representableSectionsEquiv s W u').trans
      ((congrArg E hres).trans (E.apply_symm_apply z))

end EtaleCohomology.SetSheafDescent
