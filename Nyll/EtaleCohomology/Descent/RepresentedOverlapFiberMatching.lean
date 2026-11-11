/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.RepresentedOverlapFiberSource
public import Nyll.EtaleCohomology.Descent.RepresentedFiberBaseEquality

/-!
# Original source matching on the actual double fiber

The original two source section maps, original represented overlap, and
original equality of base maps give exactly the literal double-overlap
matching equation. The comparison retains the original section itself.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {S Y T : Scheme.{u}} (q : Y ⟶ S) (t : T ⟶ S) (W : Y.Etale)
  (η : (etaleBaseChange (pullback.fst q q)).obj W ⟶
    (etaleBaseChange (pullback.snd q q)).obj W)

/-- The original source matching equation is precisely the literal
original-overlap equation on the actual double fiber. -/
theorem representedSourcePullback_overlap_matching_iff
    (a : Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W) :
    representedSectionsBaseEquality t (pullback.fst q q ≫ q) (pullback.snd q q ≫ q)
        (pullback.condition (f := q) (g := q))
        ((etaleBaseChange (pullback.snd q q)).obj W)
        (representedSourcePullback t q (pullback.fst q q) W a ≫
          (Scheme.Etale.forget (pullback q q)).map η) =
      representedSourcePullback t q (pullback.snd q q) W a ↔
    pullback.lift
        (pullback.fst (pullback.fst t q) (pullback.fst t q) ≫ a.left)
        (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
          (pullback.condition (f := t) (g := q)).symm)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => pullback.fst (pullback.fst t q) (pullback.fst t q) ≫ k)
            a.w).trans
              (FiniteEtale.relativeOverlapMap_fst q (pullback.fst t q) (pullback.snd t q) t
                (pullback.condition (f := t) (g := q)).symm).symm)) ≫ η.left =
      pullback.lift
        (pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ a.left)
        (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
          (pullback.condition (f := t) (g := q)).symm)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ k)
            a.w).trans
              (FiniteEtale.relativeOverlapMap_snd q (pullback.fst t q) (pullback.snd t q) t
                (pullback.condition (f := t) (g := q)).symm).symm)) := by
  let e := representedOverlapFiberSndIso q t
  let b := (pullback.congrHom (rfl : t = t)
    (pullback.condition (f := q) (g := q))).inv
  let u := representedSourcePullback t q (pullback.fst q q) W a
  let v := representedSourcePullback t q (pullback.snd q q) W a
  have he : e.hom ≫ b = (representedOverlapFiberFstIso q t).hom := rfl
  have hl : e.hom ≫ (b ≫ (u.left ≫ η.left)) =
      ((representedOverlapFiberFstIso q t).hom ≫ u.left) ≫ η.left := by
    simp only [← Category.assoc]
    exact congrArg (fun k => (k ≫ u.left) ≫ η.left) he
  have hu := representedOverlapFiberFstIso_source q t W a
  have hv := representedOverlapFiberSndIso_source q t W a
  constructor
  · intro h
    have hraw : b ≫ (u.left ≫ η.left) = v.left :=
      congrArg (fun k => k.left) h
    exact ((congrArg (fun k => k ≫ η.left) hu).symm.trans hl.symm).trans
      ((congrArg (fun k => e.hom ≫ k) hraw).trans hv)
  · intro h
    apply Over.OverMorphism.ext
    apply (cancel_epi e.hom).1
    change e.hom ≫ (b ≫ (u.left ≫ η.left)) = e.hom ≫ v.left
    exact hl.trans ((congrArg (fun k => k ≫ η.left) hu).trans (h.trans hv.symm))

end EtaleCohomology
