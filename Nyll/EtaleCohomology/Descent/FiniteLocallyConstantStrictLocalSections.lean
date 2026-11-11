/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
public import Nyll.EtaleCohomology.Descent.RepresentablePullbackSections
public import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Natural strict-local sections for finite locally constant coefficients

The existing represented direct-image comparison respects actual maps of
representers, as follows from its value on germs and ordinary composition
of the original scheme maps. The original section equivalence therefore
makes this comparison a natural isomorphism for qcqs morphisms.

The existing equivalence between finite étale schemes and finite locally
constant set sheaves transfers this isomorphism to the original sheaf
functors on all finite locally constant coefficients. Precomposition with
that equivalence is fully faithful, so this construction retains exactly
the represented comparison, including its original values on germs.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

private theorem representedSectionMap_naturality
    {V W : X.Etale} (k : V ⟶ W)
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    (((etaleSetPushforward f).map (X.smallEtaleTopology.yoneda.map k)).hom.app (op U)) ≫
        geometricStalkRepresentableSectionMap φ f W U v =
      geometricStalkRepresentableSectionMap φ f V U v ≫
        TypeCat.ofHom (fun a => a ≫ (Scheme.Etale.forget X).map k) := by
  apply ConcreteCategory.hom_ext
  intro a
  apply Over.OverMorphism.ext
  change geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ (a.left ≫ k.left) =
    (geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ a.left) ≫ k.left
  exact (Category.assoc _ _ _).symm

/-- The original represented direct-image stalk comparison respects
actual coefficient maps, by its existing formula on every germ. -/
theorem etaleSetPushforwardRepresentableGeometricStalkSections_naturality
    {V W : X.Etale} (k : V ⟶ W) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.map
        ((etaleSetPushforward f).map (X.smallEtaleTopology.yoneda.map k)) ≫
      etaleSetPushforwardRepresentableGeometricStalkSections φ f W =
    etaleSetPushforwardRepresentableGeometricStalkSections φ f V ≫
      TypeCat.ofHom (fun a => a ≫ (Scheme.Etale.forget X).map k) := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let η := (etaleSetPushforward f).map (X.smallEtaleTopology.yoneda.map k)
  apply Φ.presheafFiber_hom_ext
  intro U v
  let P := ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj V)).obj
  let Q := ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)).obj
  let A : Type u := Over.mk
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
      (Scheme.Etale.forget X).obj V
  let B : Type u := Over.mk
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
      (Scheme.Etale.forget X).obj W
  let sV : P.obj (op U) ⟶ Φ.presheafFiber.obj P := Φ.toPresheafFiber U v P
  let sW : Q.obj (op U) ⟶ Φ.presheafFiber.obj Q := Φ.toPresheafFiber U v Q
  let g : Φ.presheafFiber.obj P ⟶ Φ.presheafFiber.obj Q := Φ.sheafFiber.map η
  let cV : Φ.presheafFiber.obj P ⟶ A :=
    etaleSetPushforwardRepresentableGeometricStalkSections φ f V
  let cW : Φ.presheafFiber.obj Q ⟶ B :=
    etaleSetPushforwardRepresentableGeometricStalkSections φ f W
  let t : A ⟶ B := TypeCat.ofHom (fun a => a ≫ (Scheme.Etale.forget X).map k)
  have hn : sV ≫ g = η.hom.app (op U) ≫ sW :=
    Φ.toPresheafFiber_naturality η.hom U v
  have hV : sV ≫ cV = geometricStalkRepresentableSectionMap φ f V U v :=
    toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections φ f V U v
  have hW : sW ≫ cW = geometricStalkRepresentableSectionMap φ f W U v :=
    toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections φ f W U v
  change sV ≫ (g ≫ cW) = sV ≫ (cV ≫ t)
  rw [← Category.assoc, hn, Category.assoc, hW, ← Category.assoc, hV]
  exact representedSectionMap_naturality φ f k U v

/-- Naturality of the actual strict-local inverse-image section map. -/
theorem etaleSetPushforwardRepresentableStrictLocalSections_naturality
    {V W : X.Etale} (k : V ⟶ W) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.map
        ((etaleSetPushforward f).map (X.smallEtaleTopology.yoneda.map k)) ≫
      etaleSetPushforwardRepresentableStrictLocalSections φ f W =
    etaleSetPushforwardRepresentableStrictLocalSections φ f V ≫
      ((etaleSetPullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)).map
          (X.smallEtaleTopology.yoneda.map k)).hom.app (op (Scheme.Etale.mk (𝟙 _))) := by
  unfold etaleSetPushforwardRepresentableStrictLocalSections
  rw [← Category.assoc,
    etaleSetPushforwardRepresentableGeometricStalkSections_naturality, Category.assoc,
    etaleRepresentablePullbackSectionsEquiv_naturality, ← Category.assoc]

variable [QuasiCompact f] [QuasiSeparated f]

/-- On represented coefficients, the actual strict-local comparison is
a natural isomorphism between the original sheaf functors. -/
def etaleSetPushforwardYonedaStrictLocalSectionsIso :
    X.smallEtaleTopology.yoneda ⋙ etaleSetPushforward f ⋙
        (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber ≅
    X.smallEtaleTopology.yoneda ⋙
      etaleSetPullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⋙
      (sheafSections _ (Type u)).obj (op (Scheme.Etale.mk (𝟙 _))) := by
  refine NatIso.ofComponents (fun W =>
    Equiv.toIso (Equiv.ofBijective (etaleSetPushforwardRepresentableStrictLocalSections φ f W)
      (etaleSetPushforwardRepresentableStrictLocalSections_bijective φ f W))) ?_
  intro V W k
  exact etaleSetPushforwardRepresentableStrictLocalSections_naturality φ f k

/-- Finite locally constant coefficients have a natural strict-local
section comparison, extending the original represented map through the
already constructed finite-étale/FLC equivalence. -/
def etaleFiniteLocallyConstantStrictLocalSectionsIso :
    ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙ etaleSetPushforward f ⋙
        (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber ≅
    ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙
      etaleSetPullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⋙
      (sheafSections _ (Type u)).obj (op (Scheme.Etale.mk (𝟙 _))) := by
  let E := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let K := (Functor.whiskeringLeft (FiniteEtale X)
    (EtaleFiniteLocallyConstantSetSheaf X) (Type u)).obj E.functor
  exact K.preimageIso
    (Functor.isoWhiskerLeft (finiteEtaleToEtale X)
      (etaleSetPushforwardYonedaStrictLocalSectionsIso φ f))

/-- On every original finite étale representer the transferred
comparison is exactly the already constructed map, not merely a
noncanonical bijection of its source and target types. -/
theorem etaleFiniteLocallyConstantStrictLocalSectionsIso_hom_finiteEtale
    (W : FiniteEtale X) :
    (etaleFiniteLocallyConstantStrictLocalSectionsIso φ f).hom.app
        ((finiteEtaleToFiniteLocallyConstantSetSheaf X).obj W) =
      etaleSetPushforwardRepresentableStrictLocalSections φ f
        ((finiteEtaleToEtale X).obj W) := by
  let E := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let K := (Functor.whiskeringLeft (FiniteEtale X)
    (EtaleFiniteLocallyConstantSetSheaf X) (Type u)).obj E.functor
  let A := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙ etaleSetPushforward f ⋙
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
  let B := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙
    etaleSetPullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⋙
    (sheafSections _ (Type u)).obj (op (Scheme.Etale.mk (𝟙 _)))
  let e : K.obj A ≅ K.obj B := Functor.isoWhiskerLeft (finiteEtaleToEtale X)
    (etaleSetPushforwardYonedaStrictLocalSectionsIso φ f)
  have h := K.map_preimage e.hom
  exact congrArg (fun a : K.obj A ⟶ K.obj B => a.app W) h

end EtaleCohomology
