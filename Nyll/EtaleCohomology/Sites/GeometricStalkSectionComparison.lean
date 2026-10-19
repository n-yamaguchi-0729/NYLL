/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkNeighborhoodMaps
import Nyll.EtaleCohomology.Sites.PullbackSectionFactors
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The actual strict-local section comparison for direct image

The canonical maps from the constructed strictly local spectrum to all
pointed étale neighborhoods induce compatible maps from direct-image
sections to sections of actual inverse image. Descending this cocone
through the defining stalk colimit constructs the degree-zero comparison
map of Stacks Project, Theorem 59.53.1. Its value on every represented germ
is the literal inverse-image unit followed by native pullback restriction.

The construction applies to arbitrary scheme morphisms and module sheaves.
Quasi-compactness, quasi-separatedness, and properness enter only in later
proofs that the appropriate comparison maps are isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The native source base change maps to the base change of every actual
pointed étale neighborhood. -/
def geometricStalkNeighborhoodBaseChangeMap
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ⟶
      ((etaleBaseChange f).obj U).left :=
  pullback.lift
    (pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ≫
      geometricStalkNeighborhoodMap φ U v)
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t =>
        pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ≫ t)
        (geometricStalkNeighborhoodMap_comp φ U v)).trans pullback.condition))

theorem geometricStalkNeighborhoodBaseChangeMap_fst
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ pullback.fst U.hom f =
      pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ≫
        geometricStalkNeighborhoodMap φ U v := pullback.lift_fst _ _ _

theorem geometricStalkNeighborhoodBaseChangeMap_snd
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ ((etaleBaseChange f).obj U).hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f :=
  pullback.lift_snd _ _ _

/-- Native maps to source base changes respect all pointed neighborhood maps. -/
theorem geometricStalkNeighborhoodBaseChangeMap_naturality
    {U V : (Spec (CommRingCat.of R)).Etale} (a : U ⟶ V)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ ((etaleBaseChange f).map a).left =
      geometricStalkNeighborhoodBaseChangeMap φ f V
        ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v) := by
  let h : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶
      Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let m : pullback U.hom f ⟶ pullback V.hom f := ((etaleBaseChange f).map a).left
  have hm₁ : m ≫ pullback.fst V.hom f = pullback.fst U.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd V.hom f = pullback.snd U.hom f :=
    pullback.lift_snd _ _ _
  let u : pullback h f ⟶ pullback U.hom f := geometricStalkNeighborhoodBaseChangeMap φ f U v
  let w : pullback h f ⟶ pullback V.hom f := geometricStalkNeighborhoodBaseChangeMap φ f V
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v)
  have hu₁ : u ≫ pullback.fst U.hom f =
      pullback.fst h f ≫ geometricStalkNeighborhoodMap φ U v := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd U.hom f = pullback.snd h f := pullback.lift_snd _ _ _
  have hw₁ : w ≫ pullback.fst V.hom f = pullback.fst h f ≫
      geometricStalkNeighborhoodMap φ V
        ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v) :=
    pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd V.hom f = pullback.snd h f := pullback.lift_snd _ _ _
  change u ≫ m = w
  apply pullback.hom_ext
  · exact (Category.assoc u m (pullback.fst V.hom f)).trans
      ((congrArg (fun t => u ≫ t) hm₁).trans
        ((Category.assoc u (pullback.fst U.hom f) a.left).symm.trans
          ((congrArg (fun t => t ≫ a.left) hu₁).trans
            ((Category.assoc (pullback.fst h f) (geometricStalkNeighborhoodMap φ U v)
              a.left).trans
              ((congrArg (fun t => pullback.fst h f ≫ t)
                (geometricStalkNeighborhoodMap_naturality φ a v)).trans hw₁.symm)))))
  · exact (Category.assoc u m (pullback.snd V.hom f)).trans
      ((congrArg (fun t => u ≫ t) hm₂).trans (hu₂.trans hw₂.symm))

variable (Λ : Type u) [CommRing Λ]

/-- The map on sections represented on one pointed neighborhood, using
the actual inverse-image unit and the canonical native source factor. -/
def geometricStalkNeighborhoodSectionMap
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    F.obj.obj (op ((etaleBaseChange f).obj U)) ⟶
      ((etalePullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
        Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 _))) :=
  etalePullbackSectionMap _ Λ F (U := Scheme.Etale.mk (𝟙 _))
    (V := (etaleBaseChange f).obj U) (geometricStalkNeighborhoodBaseChangeMap φ f U v)
    ((geometricStalkNeighborhoodBaseChangeMap_snd φ f U v).trans
      (Category.id_comp _).symm)

/-- The actual section maps form a cocone on all pointed neighborhoods. -/
theorem geometricStalkNeighborhoodSectionMap_restriction
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U V : (Spec (CommRingCat.of R)).Etale} (a : U ⟶ V)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    F.obj.map ((etaleBaseChange f).map a).op ≫
      geometricStalkNeighborhoodSectionMap φ f Λ F U v =
        geometricStalkNeighborhoodSectionMap φ f Λ F V
          ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v) := by
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let q : pullback h f ⟶ X := pullback.snd h f
  let T : (pullback h f).Etale := Scheme.Etale.mk (𝟙 _)
  let B : X.Etale := (etaleBaseChange f).obj U
  let C : X.Etale := (etaleBaseChange f).obj V
  let m : pullback h f ⟶ B.left := geometricStalkNeighborhoodBaseChangeMap φ f U v
  let n : pullback h f ⟶ C.left := geometricStalkNeighborhoodBaseChangeMap φ f V
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v)
  let b : B ⟶ C := (etaleBaseChange f).map a
  have hm : m ≫ B.hom = T.hom ≫ q :=
    (geometricStalkNeighborhoodBaseChangeMap_snd φ f U v).trans (Category.id_comp q).symm
  have hn : n ≫ C.hom = T.hom ≫ q :=
    (geometricStalkNeighborhoodBaseChangeMap_snd φ f V _).trans (Category.id_comp q).symm
  have hmn : m ≫ b.left = n := geometricStalkNeighborhoodBaseChangeMap_naturality φ f a v
  exact etalePullbackSectionMap_restriction_of_comp_eq q Λ F
    (U := T) (V := B) (W := C) b m hm n hn hmn

/-- The canonical map from the actual direct-image stalk to global
sections after actual base change to the constructed strict-local spectrum. -/
def etalePushforwardGeometricStalkSections
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.obj
      ((etalePushforward f Λ).obj F) ⟶
        ((etalePullback
          (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
          Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 _))) :=
  (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiberDesc
    (fun U v => geometricStalkNeighborhoodSectionMap φ f Λ F U v)
    (fun _ _ a v => geometricStalkNeighborhoodSectionMap_restriction φ f Λ F a v)

/-- The strict-local comparison has the stated value on each actual
represented germ of the direct image. -/
theorem toPresheafFiber_etalePushforwardGeometricStalkSections
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
        ((etalePushforward f Λ).obj F).obj ≫ etalePushforwardGeometricStalkSections φ f Λ F =
      geometricStalkNeighborhoodSectionMap φ f Λ F U v :=
  (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_presheafFiberDesc
    _ _ U v

end EtaleCohomology
