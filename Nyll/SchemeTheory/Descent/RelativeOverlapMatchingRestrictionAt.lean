/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.RelativeOverlapMatchingSections

/-!
# Matching restriction to a specified lift

The original splitting restriction retains a separately specified lift to
the original cover, using its given equality with the splitting composite.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

variable {S Y S' Y' : Scheme.{u}} (q : Y ⟶ S)
  (q' : Y' ⟶ S') (π : Y' ⟶ Y) (t : S' ⟶ S) (hπ : π ≫ q = q' ≫ t)
  (V : Over Y)
  (η : (Over.pullback (Limits.pullback.fst q q)).obj V ⟶
    (Over.pullback (Limits.pullback.snd q q)).obj V)

/-- The actual matching restriction is bijective onto sections over the
specified lift, retaining literal precomposition by the chosen splitting. -/
theorem relativeOverlapSection_restriction_bijOn_at
    (hunit : pairHom q V η (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
    (htriple :
      pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q))
    (s : S' ⟶ Y') (hs : s ≫ q' = 𝟙 S')
    (y : S' ⟶ Y) (hsy : s ≫ π = y) :
    Set.BijOn
      (fun u : Over.mk π ⟶ V =>
        (Over.homMk (s ≫ u.left)
          (((Category.assoc _ _ _).trans (congrArg (fun k => s ≫ k) u.w)).trans hsy) :
          Over.mk y ⟶ V))
      {u | Limits.pullback.lift (Limits.pullback.fst q' q' ≫ u.left)
          (relativeOverlapMap q q' π t hπ)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => Limits.pullback.fst q' q' ≫ k) u.w).trans
              (relativeOverlapMap_fst q q' π t hπ).symm)) ≫ η.left =
        Limits.pullback.lift (Limits.pullback.snd q' q' ≫ u.left)
          (relativeOverlapMap q q' π t hπ)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => Limits.pullback.snd q' q' ≫ k) u.w).trans
              (relativeOverlapMap_snd q q' π t hπ).symm))}
      Set.univ := by
  subst y
  exact relativeOverlapSection_restriction_bijOn q q' π t hπ V η hunit htriple s hs

end AlgebraicGeometry.FiniteEtale
