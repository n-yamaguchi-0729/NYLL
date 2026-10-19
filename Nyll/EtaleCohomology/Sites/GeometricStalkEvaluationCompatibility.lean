/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkEvaluationSections
import Nyll.EtaleCohomology.Sites.GeometricStalkNeighborhoodMaps
import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
import Nyll.EtaleCohomology.Sites.PullbackComposition
import Nyll.EtaleCohomology.Sites.PullbackSectionComposition
import Nyll.EtaleCohomology.Sites.PullbackSections
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Evaluation of represented strict-local sections

The actual section comparison and evaluation commute on every represented
neighborhood section. The proof uses the actual inverse-image composition
unit and cancels its canonical composition isomorphism, then transports
along the literal equality of the source projection maps.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

private theorem sectionMap_comp_throughIso
    {X Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ] (r : Z ⟶ X) (h : p ≫ q = r)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Z.Etale} {V : Y.Etale} {W : X.Etale}
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ p)
    (m : V.left ⟶ W.left) (hm : m ≫ W.hom = V.hom ≫ q)
    (n : U.left ⟶ W.left) (hn : n ≫ W.hom = U.hom ≫ r) (hln : l ≫ m = n) :
    etalePullbackSectionMap q Λ F m hm ≫
      etaleSectionMapThroughIso Λ
        ((etalePullbackCompIso p q Λ).symm ≪≫
          eqToIso (congrArg (fun k => etalePullback k Λ) h)) F U
        (etalePullbackSectionMap p Λ ((etalePullback q Λ).obj F) l hl) =
      etalePullbackSectionMap r Λ F n hn :=
  etalePullbackSectionMap_comp_congr p q Λ r h F l hl m hm n hn hln

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (Λ : Type u) [CommRing Λ]

/-- Evaluation of the canonical strict-local neighborhood factor is the
native base change of the original geometric point in that neighborhood. -/
theorem geometricStalkEvaluationBaseChangeMap_comp_neighborhood
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkEvaluationBaseChangeMap φ f ≫
        geometricStalkNeighborhoodBaseChangeMap φ f U v =
      ((Over.pullback f).map
        (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).left := by
  let t := Spec.map (CommRingCat.ofHom φ)
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let e := Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)))
  let m := geometricStalkEvaluationBaseChangeMap φ f
  let n := geometricStalkNeighborhoodBaseChangeMap φ f U v
  let v₀ : Over.mk t ⟶ Over.mk U.hom := v
  let b : pullback t f ⟶ pullback U.hom f := ((Over.pullback f).map v₀).left
  have hb₁ : b ≫ pullback.fst U.hom f = pullback.fst t f ≫ v₀.left :=
    pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd U.hom f = pullback.snd t f :=
    pullback.lift_snd _ _ _
  have hm₁ : m ≫ pullback.fst h f = pullback.fst t f ≫ e :=
    geometricStalkEvaluationBaseChangeMap_fst φ f
  have hm₂ : m ≫ pullback.snd h f = pullback.snd t f :=
    geometricStalkEvaluationBaseChangeMap_snd φ f
  have hn₁ : n ≫ pullback.fst U.hom f =
      pullback.fst h f ≫ geometricStalkNeighborhoodMap φ U v :=
    geometricStalkNeighborhoodBaseChangeMap_fst φ f U v
  have hn₂ : n ≫ pullback.snd U.hom f = pullback.snd h f :=
    geometricStalkNeighborhoodBaseChangeMap_snd φ f U v
  have he : e ≫ geometricStalkNeighborhoodMap φ U v = v₀.left :=
    geometricStalkNeighborhoodMap_evaluation φ U v
  change m ≫ n = b
  apply pullback.hom_ext
  · exact (Category.assoc m n (pullback.fst U.hom f)).trans
      ((congrArg (fun a => m ≫ a) hn₁).trans
        ((Category.assoc m (pullback.fst h f) (geometricStalkNeighborhoodMap φ U v)).symm.trans
          ((congrArg (fun a => a ≫ geometricStalkNeighborhoodMap φ U v) hm₁).trans
            ((Category.assoc (pullback.fst t f) e (geometricStalkNeighborhoodMap φ U v)).trans
              ((congrArg (fun a => pullback.fst t f ≫ a) he).trans hb₁.symm)))))
  · exact (Category.assoc m n (pullback.snd U.hom f)).trans
      ((congrArg (fun a => m ≫ a) hn₂).trans (hm₂.trans hb₂.symm))

/-- The represented strict-local comparison followed by actual evaluation
is the literal pullback-section map through the native geometric-point factor. -/
theorem geometricStalkNeighborhoodSectionMap_evaluation
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodSectionMap φ f Λ F U v ≫
        etaleGeometricStalkEvaluationSections φ f Λ F =
      etalePullbackSectionMap
        (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) Λ F
        (U := Scheme.Etale.mk (𝟙 _)) (V := (etaleBaseChange f).obj U)
        ((Over.pullback f).map
          (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).left
        ((((Over.pullback f).map
          (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).w).trans
            (Category.id_comp _).symm) := by
  exact sectionMap_comp_throughIso
    (geometricStalkEvaluationBaseChangeMap φ f)
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ
    (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f)
    (geometricStalkEvaluationBaseChangeMap_snd φ f) F
    (U := Scheme.Etale.mk (𝟙 _)) (V := Scheme.Etale.mk (𝟙 _))
    (W := (etaleBaseChange f).obj U)
    (geometricStalkEvaluationBaseChangeMap φ f)
    ((Category.comp_id (geometricStalkEvaluationBaseChangeMap φ f)).trans
      (Category.id_comp (geometricStalkEvaluationBaseChangeMap φ f)).symm)
    (geometricStalkNeighborhoodBaseChangeMap φ f U v)
    ((geometricStalkNeighborhoodBaseChangeMap_snd φ f U v).trans
      (Category.id_comp _).symm)
    (((Over.pullback f).map
      (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).left)
    ((((Over.pullback f).map
      (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).w).trans
      (Category.id_comp _).symm)
    (geometricStalkEvaluationBaseChangeMap_comp_neighborhood φ f U v)

/-- On every represented germ, the strict-local stalk comparison followed
by evaluation is the actual section map through the native geometric factor. -/
theorem toPresheafFiber_geometricStalkSections_evaluation
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
        ((etalePushforward f Λ).obj F).obj ≫
      (etalePushforwardGeometricStalkSections φ f Λ F ≫
        etaleGeometricStalkEvaluationSections φ f Λ F) =
      etalePullbackSectionMap
        (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) Λ F
        (U := Scheme.Etale.mk (𝟙 _)) (V := (etaleBaseChange f).obj U)
        ((Over.pullback f).map
          (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).left
        ((((Over.pullback f).map
          (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).w).trans
            (Category.id_comp _).symm) := by
  exact (Category.assoc
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
      ((etalePushforward f Λ).obj F).obj)
    (etalePushforwardGeometricStalkSections φ f Λ F)
    (etaleGeometricStalkEvaluationSections φ f Λ F)).symm.trans
    ((congrArg (fun a => a ≫ etaleGeometricStalkEvaluationSections φ f Λ F)
      (toPresheafFiber_etalePushforwardGeometricStalkSections φ f Λ F U v)).trans
      (geometricStalkNeighborhoodSectionMap_evaluation φ f Λ F U v))

end EtaleCohomology
