/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentSourceComposition
public import Nyll.EtaleCohomology.Descent.GeometricStalkRepresentableSections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.SetPullbackComposition
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.Subcanonical
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Types.Basic

/-!
# The original source unit on represented direct-image stalks

The already proved formula on every original neighborhood germ determines
the source-unit square on actual direct-image stalks. The map uses the
original adjunction unit, representable pullback comparison, and
direct-image composition comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ X)

/-- The original source unit commutes with the actual represented
strict-local stalk comparison, through its original representable and
direct-image composition isomorphisms. -/
theorem etaleSetPushforwardRepresentableGeometricStalkSections_source_comp
    (W : X.Etale) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.map
        ((etaleSetPushforward f).map
          ((etaleSetPullbackPushforwardAdjunction g).unit.app
              (X.smallEtaleTopology.yoneda.obj W) ≫
            (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
          (etaleSetPushforwardCompIso g f).hom.app
            (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W))) ≫
      etaleSetPushforwardRepresentableGeometricStalkSections
        φ (g ≫ f) ((etaleBaseChange g).obj W) =
    etaleSetPushforwardRepresentableGeometricStalkSections φ f W ≫
      geometricStalkRepresentableSourcePullback φ f g W := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let Wg : Y.Etale := (etaleBaseChange g).obj W
  let F := (etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)
  let G := (etaleSetPushforward (g ≫ f)).obj (Y.smallEtaleTopology.yoneda.obj Wg)
  let η : F ⟶ G :=
    (etaleSetPushforward f).map
      ((etaleSetPullbackPushforwardAdjunction g).unit.app
          (X.smallEtaleTopology.yoneda.obj W) ≫
        (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
      (etaleSetPushforwardCompIso g f).hom.app (Y.smallEtaleTopology.yoneda.obj Wg)
  apply Φ.presheafFiber_hom_ext
  intro U v
  let P := F.obj
  let Q := G.obj
  let A : Type u := Over.mk
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
      (Scheme.Etale.forget X).obj W
  let B : Type u := Over.mk
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) (g ≫ f)) ⟶
      (Scheme.Etale.forget Y).obj Wg
  let sF : P.obj (op U) ⟶ Φ.presheafFiber.obj P := Φ.toPresheafFiber U v P
  let sG : Q.obj (op U) ⟶ Φ.presheafFiber.obj Q := Φ.toPresheafFiber U v Q
  let k : Φ.presheafFiber.obj P ⟶ Φ.presheafFiber.obj Q := Φ.sheafFiber.map η
  let cF : Φ.presheafFiber.obj P ⟶ A :=
    etaleSetPushforwardRepresentableGeometricStalkSections φ f W
  let cG : Φ.presheafFiber.obj Q ⟶ B :=
    etaleSetPushforwardRepresentableGeometricStalkSections φ (g ≫ f) Wg
  let t : A ⟶ B := geometricStalkRepresentableSourcePullback φ f g W
  have hn : sF ≫ k = η.hom.app (op U) ≫ sG :=
    Φ.toPresheafFiber_naturality η.hom U v
  have hF : sF ≫ cF = geometricStalkRepresentableSectionMap φ f W U v :=
    toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections φ f W U v
  have hG : sG ≫ cG = geometricStalkRepresentableSectionMap φ (g ≫ f) Wg U v :=
    toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections
      φ (g ≫ f) Wg U v
  have hsection : η.hom.app (op U) ≫
        geometricStalkRepresentableSectionMap φ (g ≫ f) Wg U v =
      geometricStalkRepresentableSectionMap φ f W U v ≫ t := by
    apply ConcreteCategory.hom_ext
    intro a
    exact geometricStalkRepresentableSectionMap_unit_source_comp φ f g W U v a
  change sF ≫ (k ≫ cG) = sF ≫ (cF ≫ t)
  exact (Category.assoc sF k cG).symm.trans
    ((congrArg (fun l => l ≫ cG) hn).trans
      ((Category.assoc (η.hom.app (op U)) sG cG).trans
        ((congrArg (fun l => η.hom.app (op U) ≫ l) hG).trans
          (hsection.trans
            ((congrArg (fun l => l ≫ t) hF.symm).trans (Category.assoc sF cF t))))))

end EtaleCohomology
