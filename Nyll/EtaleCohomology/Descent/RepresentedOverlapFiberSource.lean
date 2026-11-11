/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentSourceComposition
public import Nyll.SchemeTheory.Descent.AffineTransitionOverlap
public import Nyll.SchemeTheory.Descent.RelativeOverlapMatchingSections

/-!
# Original source sections on the geometric double overlap

The existing Cartesian self-overlap theorem identifies the actual double
fiber with the base change of the original overlap. The original source
pullback of a represented section then becomes its literal lift along the
map of double overlaps. Both original projections are retained.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

/-- Under an actual Cartesian source comparison, the existing represented
source map is the literal lift of the original section. -/
theorem representedSourcePullback_comp_eq_lift
    {S X Y T Z : Scheme.{u}} (h : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ X)
    (W : X.Etale) (a : Over.mk (pullback.snd h f) ⟶ (Scheme.Etale.forget X).obj W)
    (e : Z ⟶ pullback h (g ≫ f)) (d : Z ⟶ pullback h f) (δ : Z ⟶ Y)
    (he₁ : e ≫ pullback.fst h (g ≫ f) = d ≫ pullback.fst h f)
    (he₂ : e ≫ pullback.snd h (g ≫ f) = δ)
    (hd : d ≫ pullback.snd h f = δ ≫ g) :
    e ≫ (representedSourcePullback h f g W a).left =
      pullback.lift (d ≫ a.left) δ
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => d ≫ k) a.w).trans hd)) := by
  let c := (pullbackLeftPullbackSndIso h f g).inv
  let k := ((Over.pullback g).map a).left
  have hc : e ≫ c ≫ pullback.fst (pullback.snd h f) g = d := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using
        (congrArg (fun k => e ≫ k) (pullbackLeftPullbackSndIso_inv_fst h f g)).trans he₁
    · simpa only [Category.assoc] using
        (congrArg (fun k => e ≫ k)
          (pullbackLeftPullbackSndIso_inv_fst_snd h f g)).trans
            (((Category.assoc e (pullback.snd h (g ≫ f)) g).symm.trans
              (congrArg (fun k => k ≫ g) he₂)).trans hd.symm)
  have hk₁ : k ≫ pullback.fst W.hom g =
      pullback.fst (pullback.snd h f) g ≫ a.left :=
    pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd W.hom g = pullback.snd (pullback.snd h f) g :=
    ((Over.pullback g).map a).w
  change e ≫ (c ≫ k) = _
  apply pullback.hom_ext
  · exact (Category.assoc e (c ≫ k) (pullback.fst W.hom g)).trans
      ((congrArg (fun z => e ≫ z) (Category.assoc c k (pullback.fst W.hom g))).trans
        ((congrArg (fun z => e ≫ c ≫ z) hk₁).trans
          ((congrArg (fun z => e ≫ z)
            (Category.assoc c (pullback.fst (pullback.snd h f) g) a.left).symm).trans
              ((Category.assoc e (c ≫ pullback.fst (pullback.snd h f) g) a.left).symm.trans
                ((congrArg (fun z => z ≫ a.left) hc).trans
                  (pullback.lift_fst _ _ _).symm)))))
  · exact (Category.assoc e (c ≫ k) (pullback.snd W.hom g)).trans
      ((congrArg (fun z => e ≫ z) (Category.assoc c k (pullback.snd W.hom g))).trans
        ((congrArg (fun z => e ≫ c ≫ z) hk₂).trans
          ((congrArg (fun z => e ≫ z)
            (pullbackLeftPullbackSndIso_inv_snd_snd h f g)).trans
              (he₂.trans (pullback.lift_snd _ _ _).symm))))

variable {S Y T : Scheme.{u}} (q : Y ⟶ S) (t : T ⟶ S)

theorem representedOverlapFiber_isPullback :
    IsPullback
      (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
        (pullback.condition (f := t) (g := q)).symm)
      (pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ pullback.fst t q)
      (pullback.snd q q ≫ q) t :=
  AffineTransitionHom.selfOverlap_isPullback
    (pullback.snd t q) (pullback.fst t q) q t (IsPullback.of_hasPullback t q).flip

/-- The actual double fiber is the base change of the original double
overlap, with its second original projection to the base. -/
def representedOverlapFiberSndIso :
    pullback (pullback.fst t q) (pullback.fst t q) ≅
      pullback t (pullback.snd q q ≫ q) :=
  (representedOverlapFiber_isPullback q t).flip.isoPullback

@[reassoc]
theorem representedOverlapFiberSndIso_hom_fst :
    (representedOverlapFiberSndIso q t).hom ≫ pullback.fst t (pullback.snd q q ≫ q) =
      pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ pullback.fst t q :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
theorem representedOverlapFiberSndIso_hom_snd :
    (representedOverlapFiberSndIso q t).hom ≫ pullback.snd t (pullback.snd q q ≫ q) =
      FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
        (pullback.condition (f := t) (g := q)).symm :=
  IsPullback.isoPullback_hom_snd _

/-- The first-projection identification uses the original equality of
the two overlap composites to the base. -/
def representedOverlapFiberFstIso :
    pullback (pullback.fst t q) (pullback.fst t q) ≅
      pullback t (pullback.fst q q ≫ q) :=
  representedOverlapFiberSndIso q t ≪≫
    (pullback.congrHom (f₁ := t) rfl (pullback.condition (f := q) (g := q))).symm

@[reassoc]
theorem representedOverlapFiberFstIso_hom_fst :
    (representedOverlapFiberFstIso q t).hom ≫ pullback.fst t (pullback.fst q q ≫ q) =
      pullback.fst (pullback.fst t q) (pullback.fst t q) ≫ pullback.fst t q := by
  change ((representedOverlapFiberSndIso q t).hom ≫
    (pullback.congrHom (f₁ := t) rfl (pullback.condition (f := q) (g := q))).inv) ≫ _ = _
  rw [Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
    representedOverlapFiberSndIso_hom_fst]
  exact (pullback.condition (f := pullback.fst t q) (g := pullback.fst t q)).symm

@[reassoc]
theorem representedOverlapFiberFstIso_hom_snd :
    (representedOverlapFiberFstIso q t).hom ≫ pullback.snd t (pullback.fst q q ≫ q) =
      FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
        (pullback.condition (f := t) (g := q)).symm := by
  change ((representedOverlapFiberSndIso q t).hom ≫
    (pullback.congrHom (f₁ := t) rfl (pullback.condition (f := q) (g := q))).inv) ≫ _ = _
  rw [Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
    representedOverlapFiberSndIso_hom_snd]

/-- The first original source map, restricted to the actual double
fiber, is the literal first-projection lift used by the matching equation. -/
theorem representedOverlapFiberFstIso_source (W : Y.Etale)
    (a : Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W) :
    (representedOverlapFiberFstIso q t).hom ≫
        (representedSourcePullback t q (pullback.fst q q) W a).left =
      pullback.lift
        (pullback.fst (pullback.fst t q) (pullback.fst t q) ≫ a.left)
        (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
          (pullback.condition (f := t) (g := q)).symm)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => pullback.fst (pullback.fst t q) (pullback.fst t q) ≫ k)
            a.w).trans
              (FiniteEtale.relativeOverlapMap_fst q (pullback.fst t q) (pullback.snd t q) t
                (pullback.condition (f := t) (g := q)).symm).symm)) :=
  representedSourcePullback_comp_eq_lift t q (pullback.fst q q) W a
    (representedOverlapFiberFstIso q t).hom
    (pullback.fst (pullback.fst t q) (pullback.fst t q))
    (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
      (pullback.condition (f := t) (g := q)).symm)
    (representedOverlapFiberFstIso_hom_fst q t)
    (representedOverlapFiberFstIso_hom_snd q t)
    (FiniteEtale.relativeOverlapMap_fst q (pullback.fst t q) (pullback.snd t q) t
      (pullback.condition (f := t) (g := q)).symm).symm

/-- The second original source map, restricted to the actual double
fiber, is the literal second-projection lift in the same matching equation. -/
theorem representedOverlapFiberSndIso_source (W : Y.Etale)
    (a : Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W) :
    (representedOverlapFiberSndIso q t).hom ≫
        (representedSourcePullback t q (pullback.snd q q) W a).left =
      pullback.lift
        (pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ a.left)
        (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
          (pullback.condition (f := t) (g := q)).symm)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => pullback.snd (pullback.fst t q) (pullback.fst t q) ≫ k)
            a.w).trans
              (FiniteEtale.relativeOverlapMap_snd q (pullback.fst t q) (pullback.snd t q) t
                (pullback.condition (f := t) (g := q)).symm).symm)) :=
  representedSourcePullback_comp_eq_lift t q (pullback.snd q q) W a
    (representedOverlapFiberSndIso q t).hom
    (pullback.snd (pullback.fst t q) (pullback.fst t q))
    (FiniteEtale.relativeOverlapMap q (pullback.fst t q) (pullback.snd t q) t
      (pullback.condition (f := t) (g := q)).symm)
    (representedOverlapFiberSndIso_hom_fst q t)
    (representedOverlapFiberSndIso_hom_snd q t)
    (FiniteEtale.relativeOverlapMap_snd q (pullback.fst t q) (pullback.snd t q) t
      (pullback.condition (f := t) (g := q)).symm).symm

end EtaleCohomology
