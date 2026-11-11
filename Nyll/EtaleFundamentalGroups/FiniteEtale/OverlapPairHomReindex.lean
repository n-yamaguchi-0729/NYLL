/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.OverlapPairHom
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianActionPullback

/-!
# The original pair map is canonical pullback reindexing

The explicit map used by the geometric action is exactly the native
finite-étale pullback of the specified overlap isomorphism, with the
existing composition comparisons. This identifies the action cocycle
with the cocycle supplied by closed-fiber full faithfulness.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

open ProperHenselianActionLifting

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {S Y T : Scheme.{u}} (q : Y ⟶ S) (W : FiniteEtale Y)
  (θ : (FiniteEtale.pullback (Limits.pullback.fst q q)).obj W ≅
    (FiniteEtale.pullback (Limits.pullback.snd q q)).obj W)
  (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q)

/-- The explicit pair transport is the original overlap isomorphism
reindexed by the native finite-étale pullback composition comparisons. -/
theorem pairHom_eq_reindexIso_hom :
    pairHom q W.toComma θ.hom.hom a b hab =
      (reindexIso W θ (Limits.pullback.lift a b hab) a b
        (Limits.pullback.lift_fst _ _ _).symm
        (Limits.pullback.lift_snd _ _ _).symm).hom.hom := by
  let k := Limits.pullback.lift a b hab
  let c := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) k (Limits.pullback.fst q q) a
      (Limits.pullback.lift_fst a b hab).symm).app W
  let L : Limits.pullback W.hom a ⟶
      Limits.pullback W.hom (Limits.pullback.fst q q) :=
    c.hom.left ≫ Limits.pullback.fst
      (Limits.pullback.snd W.hom (Limits.pullback.fst q q)) k
  have hL : L = pairLift q W.toComma a b hab := by
    apply Limits.pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((pullbackComp_hom_app_left_fst_fst k (Limits.pullback.fst q q) a
          (Limits.pullback.lift_fst a b hab).symm W).trans
            (pairLift_fst q W.toComma a b hab).symm)
    · have hc : c.hom.left ≫ Limits.pullback.snd
          (Limits.pullback.snd W.hom (Limits.pullback.fst q q)) k =
          Limits.pullback.snd W.hom a := c.hom.w
      change (c.hom.left ≫ Limits.pullback.fst
        (Limits.pullback.snd W.hom (Limits.pullback.fst q q)) k) ≫
          Limits.pullback.snd W.hom (Limits.pullback.fst q q) = _
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun r => c.hom.left ≫ r)
          (Limits.pullback.condition
            (f := Limits.pullback.snd W.hom (Limits.pullback.fst q q)) (g := k))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun r => r ≫ k) hc).trans
              (pairLift_snd q W.toComma a b hab).symm)))
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · have h := reindexIso_hom_left_fst W θ k a b
      (Limits.pullback.lift_fst a b hab).symm (Limits.pullback.lift_snd a b hab).symm
    have h' := congrArg (fun r => r ≫ θ.hom.left ≫
      Limits.pullback.fst W.hom (Limits.pullback.snd q q)) hL
    exact (pairHom_fst q W.toComma θ.hom.hom a b hab).trans
      (h'.symm.trans ((Category.assoc _ _ _).trans h.symm))
  · exact (pairHom_snd q W.toComma θ.hom.hom a b hab).trans
      ((reindexIso W θ k a b (Limits.pullback.lift_fst a b hab).symm
        (Limits.pullback.lift_snd a b hab).symm).hom.w).symm

end AlgebraicGeometry.FiniteEtale
