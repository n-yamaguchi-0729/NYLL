/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Represented fiber sections in an actual cartesian restriction square

Pullback pasting and the existing slice adjunction give the equivalence
between sections of the original representer on the original geometric
fiber and sections of its base change. The original representer projection
computes its value.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {S U Y P T : Scheme.{u}} (i : U ⟶ S) (q : Y ⟶ S)
  (p : P ⟶ U) (g : P ⟶ Y) (H : IsPullback p g i q)
  (r : T ⟶ U) (W : Y.Etale)

/-- The existing pullback-pasting isomorphism on the original fibers,
retained as an isomorphism over the original cover. -/
def representedFiberRestrictionSourceIso :
    Over.mk (pullback.snd r p ≫ g) ≅ Over.mk (pullback.snd (r ≫ i) q) :=
  Over.isoMk ((IsPullback.of_hasPullback r p).paste_vert H).isoPullback
    ((IsPullback.of_hasPullback r p).paste_vert H).isoPullback_hom_snd

/-- Actual represented fiber sections agree across a cartesian base
restriction, by pullback pasting and the existing slice adjunction. -/
def representedFiberRestrictionEquiv :
    (Over.mk (pullback.snd (r ≫ i) q) ⟶ (Scheme.Etale.forget Y).obj W) ≃
      (Over.mk (pullback.snd r p) ⟶
        (Scheme.Etale.forget P).obj ((etaleBaseChange g).obj W)) :=
  ((representedFiberRestrictionSourceIso i q p g H r).symm.homCongr
    (Iso.refl ((Scheme.Etale.forget Y).obj W))).trans
      ((Over.mapPullbackAdj g).homEquiv (Over.mk (pullback.snd r p))
        ((Scheme.Etale.forget Y).obj W))

/-- The equivalence retains the original map to the representer after
projection from its base change. -/
theorem representedFiberRestrictionEquiv_fst
    (a : Over.mk (pullback.snd (r ≫ i) q) ⟶ (Scheme.Etale.forget Y).obj W) :
    (representedFiberRestrictionEquiv i q p g H r W a).left ≫ pullback.fst W.hom g =
      ((IsPullback.of_hasPullback r p).paste_vert H).isoPullback.hom ≫ a.left := by
  change (((Over.mapPullbackAdj g).homEquiv (Over.mk (pullback.snd r p))
    ((Scheme.Etale.forget Y).obj W))
      (((representedFiberRestrictionSourceIso i q p g H r).hom ≫ a) ≫ 𝟙 _)).left ≫ _ = _
  simp only [Category.comp_id, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

/-- The second projection of the transported section remains its
original map to the restricted cover. -/
theorem representedFiberRestrictionEquiv_snd
    (a : Over.mk (pullback.snd (r ≫ i) q) ⟶ (Scheme.Etale.forget Y).obj W) :
    (representedFiberRestrictionEquiv i q p g H r W a).left ≫ pullback.snd W.hom g =
      pullback.snd r p :=
  (representedFiberRestrictionEquiv i q p g H r W a).w

end EtaleCohomology
