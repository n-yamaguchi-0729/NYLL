/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentSecondArrow
public import Nyll.EtaleCohomology.Descent.SetSheafDescentStalkSourceComposition

public import Nyll.EtaleCohomology.Sites.RepresentablePullback
public import Nyll.EtaleCohomology.Sites.SetPullbackComposition
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Descent.SetSheafDescentSourceComposition
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Actual represented sections of the second matching arrow

The original overlap map and original direct-image comparisons give an
explicit target isomorphism. Under it, the second matching arrow is the
original source unit for the second overlap projection. The existing
section and stalk formulas therefore apply to the actual matching arrow.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology.SetSheafDescent

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (W : Y.Etale)
  (θ : (etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W) ≅
    (etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W))

/-- Every factor of the specified target comparison is the original
 isomorphism or its original direct image. -/
theorem representedOverlapArrowTarget_isIso :
    IsIso (((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
    (etaleSetPushforward (pullback.fst q q ≫ q)).map θ.hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom)) := by
  infer_instance

/-- After the displayed actual target comparison, the second matching
 arrow is the original unit and original composition comparison. -/
theorem secondArrow_representedOverlapArrowTarget :
    secondArrow q (Y.smallEtaleTopology.yoneda.obj W) θ ≫
        ((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
    (etaleSetPushforward (pullback.fst q q ≫ q)).map θ.hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom) =
      (etaleSetPushforward q).map
          ((etaleSetPullbackPushforwardAdjunction (pullback.snd q q)).unit.app
              (Y.smallEtaleTopology.yoneda.obj W) ≫
            (etaleSetPushforward (pullback.snd q q)).map
              (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom) ≫
        (etaleSetPushforwardCompIso (pullback.snd q q) q).hom.app
          ((pullback q q).smallEtaleTopology.yoneda.obj
            ((etaleBaseChange (pullback.snd q q)).obj W)) :=
  secondArrow_comp_overlap_pushforward_map q (Y.smallEtaleTopology.yoneda.obj W) θ
    ((pullback q q).smallEtaleTopology.yoneda.obj
      ((etaleBaseChange (pullback.snd q q)).obj W))
    (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom

/-- On an original represented section, the actual second matching
arrow is the second-projection pullback of that section. -/
theorem secondArrow_representedOverlapArrowTarget_app
    (U : X.Etale) (a : (etaleBaseChange q).obj U ⟶ W) :
    (secondArrow q (Y.smallEtaleTopology.yoneda.obj W) θ ≫
        ((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
    (etaleSetPushforward (pullback.fst q q ≫ q)).map θ.hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom)).hom.app (op U) a =
      (MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
          (pullback.snd q q) q).hom.app U ≫
        (etaleBaseChange (pullback.snd q q)).map a := by
  have h := secondArrow_representedOverlapArrowTarget q W θ
  exact (congrArg (fun b :
    (etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W) ⟶
      (etaleSetPushforward (pullback.snd q q ≫ q)).obj
        ((pullback q q).smallEtaleTopology.yoneda.obj
          ((etaleBaseChange (pullback.snd q q)).obj W)) => b.hom.app (op U) a) h).trans
    (etaleSetPushforward_unit_yoneda_comp_app q (pullback.snd q q) W U a)

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R))
  (V : Z.Etale)
  (ψ : (etaleSetPullback (pullback.fst f f)).obj (Z.smallEtaleTopology.yoneda.obj V) ≅
    (etaleSetPullback (pullback.snd f f)).obj (Z.smallEtaleTopology.yoneda.obj V))

/-- The actual second matching arrow respects the original represented
strict-local stalk comparison, through its specified target isomorphism. -/
theorem secondArrow_representedOverlapArrowTarget_stalk :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.map
        (secondArrow f (Z.smallEtaleTopology.yoneda.obj V) ψ ≫
          ((etaleSetPushforwardCompIso (pullback.fst f f) f).hom.app
      ((etaleSetPullback (pullback.fst f f)).obj (Z.smallEtaleTopology.yoneda.obj V)) ≫
    (etaleSetPushforward (pullback.fst f f ≫ f)).map ψ.hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := f) (g := f)))).hom.app
          ((etaleSetPullback (pullback.snd f f)).obj (Z.smallEtaleTopology.yoneda.obj V)) ≫
        (etaleSetPushforward (pullback.snd f f ≫ f)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd f f) V).hom)) ≫
      etaleSetPushforwardRepresentableGeometricStalkSections
        φ (pullback.snd f f ≫ f) ((etaleBaseChange (pullback.snd f f)).obj V) =
    etaleSetPushforwardRepresentableGeometricStalkSections φ f V ≫
      geometricStalkRepresentableSourcePullback φ f (pullback.snd f f) V := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let c := etaleSetPushforwardRepresentableGeometricStalkSections
    φ (pullback.snd f f ≫ f) ((etaleBaseChange (pullback.snd f f)).obj V)
  have h := secondArrow_representedOverlapArrowTarget f V ψ
  exact (congrArg (fun a => Φ.sheafFiber.map a ≫ c) h).trans
    (etaleSetPushforwardRepresentableGeometricStalkSections_source_comp
      φ f (pullback.snd f f) V)

end EtaleCohomology.SetSheafDescent
