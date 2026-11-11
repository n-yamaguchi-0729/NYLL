/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.GeometricStalkSectionDescent
public import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Represented direct-image germs and strict-local sections

The native maps from the strict-local source to pointed étale
neighborhoods give an actual map from direct-image germs of a represented
étale sheaf to sections of its representer over the strict-local source.
Every such section is the image of a germ when the original morphism is
quasi-compact and quasi-separated, by the existing finite-presentation
scheme descent and the actual affine-neighborhood refinement.

No properness or finite étale hypothesis is needed for this existence
step. Injectivity and comparison with the closed geometric fibre are
separate assertions.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (W : X.Etale)

/-- Restriction of one actual represented section along the native
strict-local map associated to its pointed neighborhood. -/
def geometricStalkRepresentableSectionMap
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)).obj.obj (op U) ⟶
      (Over.mk
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
          (Scheme.Etale.forget X).obj W) :=
  TypeCat.ofHom (fun a =>
    Over.homMk (geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ a.left)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ k) a.w).trans
          (geometricStalkNeighborhoodBaseChangeMap_snd φ f U v))))

/-- These actual section restrictions respect maps of pointed neighborhoods. -/
theorem geometricStalkRepresentableSectionMap_restriction
    {U V : (Spec (CommRingCat.of R)).Etale} (a : U ⟶ V)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)).obj.map a.op ≫
        geometricStalkRepresentableSectionMap φ f W U v =
      geometricStalkRepresentableSectionMap φ f W V
        ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v) := by
  apply ConcreteCategory.hom_ext
  intro b
  apply Over.OverMorphism.ext
  change geometricStalkNeighborhoodBaseChangeMap φ f U v ≫
      (((etaleBaseChange f).map a).left ≫ b.left) =
    geometricStalkNeighborhoodBaseChangeMap φ f V
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v) ≫ b.left
  rw [← Category.assoc, geometricStalkNeighborhoodBaseChangeMap_naturality]

/-- The original direct-image stalk maps to actual strict-local sections
of the represented étale scheme. -/
def etaleSetPushforwardRepresentableGeometricStalkSections :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.obj
      ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)) ⟶
        (Over.mk
          (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
            (Scheme.Etale.forget X).obj W) :=
  (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiberDesc
    (fun U v => geometricStalkRepresentableSectionMap φ f W U v)
    (fun _ _ a v => geometricStalkRepresentableSectionMap_restriction φ f W a v)

/-- The stalk comparison retains its literal value on represented germs. -/
theorem toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
        ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)).obj ≫
      etaleSetPushforwardRepresentableGeometricStalkSections φ f W =
        geometricStalkRepresentableSectionMap φ f W U v :=
  (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_presheafFiberDesc
    _ _ U v

/-- Every strict-local section of an étale representer comes from an
actual direct-image germ for a quasi-compact quasi-separated morphism. -/
theorem etaleSetPushforwardRepresentableGeometricStalkSections_surjective
    [QuasiCompact f] [QuasiSeparated f] :
    Function.Surjective (etaleSetPushforwardRepresentableGeometricStalkSections φ f W) := by
  intro a
  obtain ⟨U, v, hU, b, m, hb, hrec, hm₂, hm₁⟩ :=
    geometricStalk_exists_affine_section_stage φ f W.hom a.left a.w
  have : IsAffine U.left := hU
  have hm : m = geometricStalkNeighborhoodBaseChangeMap φ f U v := by
    apply pullback.hom_ext
    · exact hm₁.trans
        ((congrArg (fun k =>
          pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ≫ k)
          (geometricStalkNeighborhoodMap_eq_germ φ U v)).symm.trans
            (geometricStalkNeighborhoodBaseChangeMap_fst φ f U v).symm)
    · exact hm₂.trans (geometricStalkNeighborhoodBaseChangeMap_snd φ f U v).symm
  let b' : (etaleBaseChange f).obj U ⟶ W := MorphismProperty.Over.homMk b hb
  refine ⟨(Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
    ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)).obj b', ?_⟩
  have heval := ConcreteCategory.congr_hom
    (toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections φ f W U v) b'
  change etaleSetPushforwardRepresentableGeometricStalkSections φ f W
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
        ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)).obj b') =
    geometricStalkRepresentableSectionMap φ f W U v b' at heval
  apply heval.trans
  apply Over.OverMorphism.ext
  exact (congrArg (fun k => k ≫ b) hm.symm).trans hrec

end EtaleCohomology
