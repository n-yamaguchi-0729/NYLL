/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.GeometricStalkRepresentableSectionsBijective
public import Nyll.EtaleCohomology.Sites.PullbackSectionFactors
public import Nyll.EtaleCohomology.Sites.RepresentablePullback
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.Subcanonical
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Actual represented sections and inverse-image global sections

The existing slice adjunction and representable inverse-image comparison
identify a morphism to the original representer with a global section of
its actual inverse image. The comparison is computed by the existing
small-site base-change lift and is natural in the represented étale scheme.

Applied to the constructed strict-local base change, this transports the
proved represented direct-image stalk bijection to the actual global
sections of the original sheaf inverse image, retaining its value on germs.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : Y ⟶ X)

/-- Morphisms over the base identify with sections of the actual étale
base change through the existing slice adjunction. -/
def overSectionEquivEtaleSection (W : X.Etale) :
    (Over.mk q ⟶ (Scheme.Etale.forget X).obj W) ≃
      ((Scheme.Etale.mk (𝟙 Y) : Y.Etale) ⟶ (etaleBaseChange q).obj W) := by
  let e : (Over.map q).obj (Over.mk (𝟙 Y)) ≅ Over.mk q :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 Y) ≫ q = (𝟙 Y) ≫ q
      rfl)
  let FF : (Scheme.Etale.forget Y).FullyFaithful :=
    MorphismProperty.Comma.forgetFullyFaithful (𝟭 Scheme.{u}) (Functor.fromPUnit Y)
      (show MorphismProperty Scheme.{u} from @Etale)
  exact (Iso.homCongr e.symm (Iso.refl _)).trans
    (((Over.mapPullbackAdj q).homEquiv (Over.mk (𝟙 Y))
      ((Scheme.Etale.forget X).obj W)).trans
        (FF.homEquiv (X := Scheme.Etale.mk (𝟙 Y))
          (Y := (etaleBaseChange q).obj W)).symm)

private theorem overSectionEquivEtaleSection_apply (W : X.Etale)
    (a : Over.mk q ⟶ (Scheme.Etale.forget X).obj W) :
    overSectionEquivEtaleSection q W a =
      etaleBaseChangeLift q a.left (a.w.trans (Category.id_comp q).symm) := by
  apply MorphismProperty.Over.Hom.ext
  dsimp only [overSectionEquivEtaleSection, Equiv.trans_apply]
  simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  change pullback.lift ((𝟙 Y) ≫ a.left ≫ (𝟙 W.left)) (𝟙 Y) _ =
    pullback.lift a.left (𝟙 Y) _
  simp only [Category.id_comp]
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans
      ((Category.comp_id a.left).trans (pullback.lift_fst _ _ _).symm)
  · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- Actual morphisms into an étale representer are global sections of
the original inverse-image sheaf, via the existing slice adjunction. -/
def etaleRepresentablePullbackSectionsEquiv (W : X.Etale) :
    (Over.mk q ⟶ (Scheme.Etale.forget X).obj W) ≃
      ((etaleSetPullback q).obj (X.smallEtaleTopology.yoneda.obj W)).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y))) :=
  (overSectionEquivEtaleSection q W).trans
    ((((sheafSections Y.smallEtaleTopology (Type u)).obj
      (op (Scheme.Etale.mk (𝟙 Y)))).mapIso
        (etaleSetPullbackYonedaObjIso q W)).symm.toEquiv)

/-- Under the original representable comparison, the resulting section
is the actual base-change lift of the original scheme morphism. -/
theorem etaleRepresentablePullbackSectionsEquiv_yoneda
    (W : X.Etale) (a : Over.mk q ⟶ (Scheme.Etale.forget X).obj W) :
    (etaleSetPullbackYonedaObjIso q W).hom.hom.app (op (Scheme.Etale.mk (𝟙 Y)))
        (etaleRepresentablePullbackSectionsEquiv q W a) =
      etaleBaseChangeLift q a.left (a.w.trans (Category.id_comp q).symm) := by
  let E := ((sheafSections Y.smallEtaleTopology (Type u)).obj
    (op (Scheme.Etale.mk (𝟙 Y)))).mapIso (etaleSetPullbackYonedaObjIso q W)
  change E.toEquiv (E.toEquiv.symm (overSectionEquivEtaleSection q W a)) = _
  rw [Equiv.apply_symm_apply]
  exact overSectionEquivEtaleSection_apply q W a

private theorem overSectionEquivEtaleSection_naturality
    {V W : X.Etale} (k : V ⟶ W) :
    TypeCat.ofHom (fun a : Over.mk q ⟶ (Scheme.Etale.forget X).obj V =>
      a ≫ (Scheme.Etale.forget X).map k) ≫
        (overSectionEquivEtaleSection q W).toIso.hom =
    (overSectionEquivEtaleSection q V).toIso.hom ≫
      TypeCat.ofHom (fun a : Scheme.Etale.mk (𝟙 Y) ⟶ (etaleBaseChange q).obj V =>
        a ≫ (etaleBaseChange q).map k) := by
  apply ConcreteCategory.hom_ext
  intro a
  change overSectionEquivEtaleSection q W (a ≫ (Scheme.Etale.forget X).map k) =
    overSectionEquivEtaleSection q V a ≫ (etaleBaseChange q).map k
  rw [overSectionEquivEtaleSection_apply, overSectionEquivEtaleSection_apply]
  have ha : a.left ≫ V.hom = (𝟙 Y) ≫ q :=
    a.w.trans (Category.id_comp q).symm
  have hak : (a.left ≫ k.left) ≫ W.hom = (𝟙 Y) ≫ q :=
    (Category.assoc a.left k.left W.hom).trans
      ((congrArg (fun m => a.left ≫ m) k.w).trans ha)
  exact (etaleBaseChangeLift_comp (U := Scheme.Etale.mk (𝟙 Y))
    (V := V) (W := W) q k a.left ha hak).symm

/-- The comparison is natural in the represented étale scheme, using
the original sheaf inverse-image map and actual postcomposition. -/
theorem etaleRepresentablePullbackSectionsEquiv_naturality
    {V W : X.Etale} (k : V ⟶ W) :
    TypeCat.ofHom (fun a : Over.mk q ⟶ (Scheme.Etale.forget X).obj V =>
      a ≫ (Scheme.Etale.forget X).map k) ≫
        (etaleRepresentablePullbackSectionsEquiv q W).toIso.hom =
    (etaleRepresentablePullbackSectionsEquiv q V).toIso.hom ≫
      ((etaleSetPullback q).map (X.smallEtaleTopology.yoneda.map k)).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) := by
  let E := Functor.isoWhiskerRight (etaleSetPullbackYonedaIso q)
    ((sheafSections Y.smallEtaleTopology (Type u)).obj (op (Scheme.Etale.mk (𝟙 Y))))
  let a := TypeCat.ofHom (fun a : Over.mk q ⟶ (Scheme.Etale.forget X).obj V =>
    a ≫ (Scheme.Etale.forget X).map k)
  let b := TypeCat.ofHom
    (fun a : Scheme.Etale.mk (𝟙 Y) ⟶ (etaleBaseChange q).obj V =>
      a ≫ (etaleBaseChange q).map k)
  let c := ((etaleSetPullback q).map (X.smallEtaleTopology.yoneda.map k)).hom.app
    (op (Scheme.Etale.mk (𝟙 Y)))
  have hn : b ≫ E.inv.app W = E.inv.app V ≫ c := E.inv.naturality k
  have hr : a ≫ (overSectionEquivEtaleSection q W).toIso.hom =
      (overSectionEquivEtaleSection q V).toIso.hom ≫ b :=
    overSectionEquivEtaleSection_naturality q k
  change a ≫ ((overSectionEquivEtaleSection q W).toIso.hom ≫ E.inv.app W) =
    ((overSectionEquivEtaleSection q V).toIso.hom ≫ E.inv.app V) ≫ c
  rw [← Category.assoc, hr, Category.assoc, hn, ← Category.assoc]

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of R))

/-- The represented direct-image stalk maps to the actual global
sections of the original sheaf inverse image on the strict-local source. -/
def etaleSetPushforwardRepresentableStrictLocalSections (W : S.Etale) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.obj
      ((etaleSetPushforward f).obj (S.smallEtaleTopology.yoneda.obj W)) ⟶
    ((etaleSetPullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)).obj
        (S.smallEtaleTopology.yoneda.obj W)).obj.obj (op (Scheme.Etale.mk (𝟙 _))) :=
  etaleSetPushforwardRepresentableGeometricStalkSections φ f W ≫
    (etaleRepresentablePullbackSectionsEquiv
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) W).toIso.hom

/-- The actual inverse-image H⁰ comparison retains its literal value on
every original pointed-neighborhood germ. -/
theorem toPresheafFiber_etaleSetPushforwardRepresentableStrictLocalSections
    (W : S.Etale) (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
        ((etaleSetPushforward f).obj (S.smallEtaleTopology.yoneda.obj W)).obj ≫
      etaleSetPushforwardRepresentableStrictLocalSections φ f W =
    geometricStalkRepresentableSectionMap φ f W U v ≫
      (etaleRepresentablePullbackSectionsEquiv
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
        W).toIso.hom :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫
      (etaleRepresentablePullbackSectionsEquiv
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) W).toIso.hom)
      (toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections φ f W U v))

/-- For a qcqs source, represented direct-image germs are exactly the
actual global sections of the original strict-local inverse image. -/
theorem etaleSetPushforwardRepresentableStrictLocalSections_bijective
    [QuasiCompact f] [QuasiSeparated f] (W : S.Etale) :
    Function.Bijective (etaleSetPushforwardRepresentableStrictLocalSections φ f W) :=
  (etaleRepresentablePullbackSectionsEquiv
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) W).bijective.comp
      (etaleSetPushforwardRepresentableGeometricStalkSections_bijective φ f W)

end EtaleCohomology
