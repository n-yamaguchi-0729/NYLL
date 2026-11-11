/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSectionMaps
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks

/-!
# Geometric stalks of ordinary étale restriction

The existing inverse-image unit/component theorem applies to the actual
restriction adjunction. Its inverse identifies the restricted stalk with
the original stalk. The original section-unit calculation shows that this
identification sends each germ to the same section on the postcomposed
pointed étale neighborhood.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {U X : Scheme.{u}} (i : U ⟶ X) [Etale i]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (r : Spec (CommRingCat.of Ω) ⟶ U)
  (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A] [HasProducts.{u} A]

/-- Ordinary étale restriction preserves the actual stalk at a specified geometric lift. -/
def etaleRestrictionGeometricStalkIso (H : Sheaf X.smallEtaleTopology A) :
    (Scheme.pointSmallEtale r).sheafFiber.obj ((etaleRestriction i A).obj H) ≅
      (Scheme.pointSmallEtale (r ≫ i)).sheafFiber.obj H := by
  let k := (Scheme.pointSmallEtale (r ≫ i)).sheafFiber.map
      ((etaleRestrictionPushforwardAdjunction i A).unit.app H) ≫
    etalePushforwardStalkComponent i (r ≫ i) ⟨r, rfl⟩ ((etaleRestriction i A).obj H)
  have : IsIso k := etalePullbackUnit_stalkComponent_isIso_generic i r A
    (etaleRestriction i A) (etaleRestrictionPushforwardAdjunction i A) H
  exact (asIso k).symm

/-- The restriction stalk isomorphism retains the literal pointed neighborhood
and the original section representing every germ. -/
theorem toPresheafFiber_etaleRestrictionGeometricStalkIso
    (H : Sheaf X.smallEtaleTopology A) (V : U.Etale)
    (v : (Scheme.pointSmallEtale r).fiber.obj V) :
    (Scheme.pointSmallEtale r).toPresheafFiber V v ((etaleRestriction i A).obj H).obj ≫
        (etaleRestrictionGeometricStalkIso i r A H).hom =
      (Scheme.pointSmallEtale (r ≫ i)).toPresheafFiber ((etalePostcompose i).obj V)
        (Over.homMk v.left ((Category.assoc v.left V.hom i).symm.trans
          (congrArg (fun z : Spec (CommRingCat.of Ω) ⟶ U => z ≫ i) v.w))) H.obj := by
  let W := (etalePostcompose i).obj V
  let L := etaleRestriction i A
  let adj := etaleRestrictionPushforwardAdjunction i A
  let e := etaleRestrictionGeometricStalkIso i r A H
  let hl : (𝟙 V.left) ≫ W.hom = V.hom ≫ i := Category.id_comp _
  let j : V ⟶ (etaleBaseChange i).obj W := etaleBaseChangeLift i (𝟙 V.left) hl
  have hc : (etalePostcompose i).map j ≫
      (etalePostcomposeBaseChangeAdjunction i).counit.app W = 𝟙 W := by
    refine (etalePostcomposeBaseChangeLift_counit i (U := W) (V := V) (𝟙 V.left) hl).trans ?_
    apply MorphismProperty.Over.Hom.ext
    rfl
  have hsec : (adj.unit.app H).hom.app (op W) ≫
      (L.obj H).obj.map j.op = 𝟙 (H.obj.obj (op W)) := by
    have hu : (adj.unit.app H).hom.app (op W) =
        H.obj.map ((etalePostcomposeBaseChangeAdjunction i).counit.app W).op :=
      etaleRestrictionUnit_app i H W
    have hm : (L.obj H).obj.map j.op = H.obj.map ((etalePostcompose i).map j).op := rfl
    exact (congrArg (fun a => a ≫ (L.obj H).obj.map j.op) hu).trans
      ((congrArg (fun a =>
        H.obj.map ((etalePostcomposeBaseChangeAdjunction i).counit.app W).op ≫ a) hm).trans
        ((H.obj.map_comp _ _).symm.trans
          ((congrArg (fun a : W ⟶ W => H.obj.map a.op) hc).trans
            (H.obj.map_id (op W)))))
  have hg := etalePullbackSectionMap_toPresheafFiber_generic i r A L adj H
    (U := V) (V := W) (𝟙 V.left) hl v
  let a : (Scheme.pointSmallEtale (r ≫ i)).fiber.obj W :=
    Over.homMk v.left ((Category.assoc v.left V.hom i).symm.trans
      (congrArg (fun z : Spec (CommRingCat.of Ω) ⟶ U => z ≫ i) v.w))
  let a' : (Scheme.pointSmallEtale (r ≫ i)).fiber.obj W :=
    Over.homMk (v.left ≫ 𝟙 V.left)
      ((Category.assoc v.left (𝟙 V.left) W.hom).trans
        ((congrArg (fun z : V.left ⟶ X => v.left ≫ z) hl).trans
          ((Category.assoc v.left V.hom i).symm.trans
            (congrArg (fun z : Spec (CommRingCat.of Ω) ⟶ U => z ≫ i) v.w))))
  have ha : a' = a := Over.OverMorphism.ext (Category.comp_id v.left)
  let γU : H.obj.obj (op W) ⟶ (Scheme.pointSmallEtale r).sheafFiber.obj (L.obj H) :=
    (Scheme.pointSmallEtale r).toPresheafFiber V v (L.obj H).obj
  let γS : H.obj.obj (op W) ⟶ (Scheme.pointSmallEtale (r ≫ i)).sheafFiber.obj H :=
    (Scheme.pointSmallEtale (r ≫ i)).toPresheafFiber W a H.obj
  have hg' : ((adj.unit.app H).hom.app (op W) ≫ (L.obj H).obj.map j.op) ≫ γU =
      (Scheme.pointSmallEtale (r ≫ i)).toPresheafFiber W a' H.obj ≫ e.inv := hg
  have hleft : ((adj.unit.app H).hom.app (op W) ≫ (L.obj H).obj.map j.op) ≫ γU = γU :=
    (congrArg (fun z : H.obj.obj (op W) ⟶ H.obj.obj (op W) => z ≫ γU) hsec).trans
      (Category.id_comp γU)
  have hright : (Scheme.pointSmallEtale (r ≫ i)).toPresheafFiber W a' H.obj ≫ e.inv =
      γS ≫ e.inv := congrArg (fun z : (Scheme.pointSmallEtale (r ≫ i)).fiber.obj W =>
        (Scheme.pointSmallEtale (r ≫ i)).toPresheafFiber W z H.obj ≫ e.inv) ha
  have hγ : γU = γS ≫ e.inv := hleft.symm.trans (hg'.trans hright)
  change γU ≫ e.hom = γS
  exact (congrArg (fun z : H.obj.obj (op W) ⟶
      (Scheme.pointSmallEtale r).sheafFiber.obj (L.obj H) => z ≫ e.hom) hγ).trans
    ((Category.assoc γS e.inv e.hom).trans
      ((congrArg (fun z : (Scheme.pointSmallEtale (r ≫ i)).sheafFiber.obj H ⟶
          (Scheme.pointSmallEtale (r ≫ i)).sheafFiber.obj H => γS ≫ z) e.inv_hom_id).trans
        (Category.comp_id γS)))

end EtaleCohomology
