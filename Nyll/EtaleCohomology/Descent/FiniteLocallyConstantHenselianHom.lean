/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
public import Nyll.EtaleCohomology.Constructible.Representability
public import Nyll.EtaleCohomology.Sites.RepresentablePullback
public import Nyll.EtaleFundamentalGroups.Cohomology.RepresenterPullback
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianFullyFaithful
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.Logic.Function.Basic

/-!
# Henselian comparison for finite locally constant set sheaves

The actual inverse-image functor on set-valued étale sheaves induces a
bijection on morphisms between finite locally constant sheaves over a proper
scheme over an arbitrary henselian local ring. The proof uses their existing
finite étale representers and the already proved proper henselian theorem
for finite étale morphisms. The natural representable inverse-image
comparison identifies the map with the original sheaf inverse image.

This supplies the finite locally constant coefficient case of the
henselian degree-zero comparison without copying the module-valued proof.
It does not assert essential surjectivity or proper descent of objects.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Opposite

universe u

namespace EtaleCohomology

/-- The natural representable comparison transfers finite étale full
faithfulness to the actual inverse image on finite locally constant sheaves. -/
theorem etaleSetPullback_map_bijective_of_finiteEtaleFullyFaithful
    {X Y : Scheme.{u}} (i : Y ⟶ X)
    (hFE : (FiniteEtale.pullback i).FullyFaithful)
    {F G : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsEtaleFiniteLocallyConstantSet F)
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    Function.Bijective ((etaleSetPullback i).map : (F ⟶ G) → _) := by
  let P := etaleSetPullback i
  let hcomp : (finiteEtaleSheaf X ⋙ P).FullyFaithful :=
    (hFE.comp (finiteEtaleSheafFullyFaithful _)).ofIso
      (EtaleFundamentalGroups.Cohomology.finiteEtaleSheafPullbackIso i).symm
  have hrep (A B : FiniteEtale X) :
      Function.Bijective (P.map :
        ((finiteEtaleSheaf X).obj A ⟶ (finiteEtaleSheaf X).obj B) → _) :=
    (Function.Bijective.of_comp_iff _
      ((finiteEtaleSheafFullyFaithful X).map_bijective A B)).mp
        (hcomp.map_bijective A B)
  obtain ⟨A, ⟨eA⟩⟩ := hF.exists_finiteEtaleSheaf_iso
  obtain ⟨B, ⟨eB⟩⟩ := hG.exists_finiteEtaleSheaf_iso
  change Function.Bijective (P.map : (F ⟶ G) → _)
  constructor
  · intro a b hab
    have heq : eA.hom ≫ a ≫ eB.inv = eA.hom ≫ b ≫ eB.inv :=
      (hrep A B).injective (by
        simp only [Functor.map_comp, hab])
    exact (cancel_epi eA.hom).mp ((cancel_mono eB.inv).mp
      (by simpa only [Category.assoc] using heq))
  · intro a
    obtain ⟨b, hb⟩ := (hrep A B).surjective
      (P.map eA.hom ≫ a ≫ P.map eB.inv)
    refine ⟨eA.inv ≫ b ≫ eB.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, hb]
    change (P.mapIso eA).inv ≫
      ((P.mapIso eA).hom ≫ a ≫ (P.mapIso eB).inv) ≫ (P.mapIso eB).hom = a
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- On finite locally constant set sheaves, the original closed-fibre
inverse image is bijective on Hom over every proper henselian family.
Neither noetherianity nor flatness of the proper family is required. -/
theorem etaleSetPullback_closedFiber_map_bijective
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {F G : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsEtaleFiniteLocallyConstantSet F)
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    Function.Bijective
      ((etaleSetPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).map :
        (F ⟶ G) → _) :=
  etaleSetPullback_map_bijective_of_finiteEtaleFullyFaithful _
    (FiniteEtale.pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing f) hF hG

/-- Finite étale full faithfulness makes the actual inverse-image unit
bijective on finite étale sections of finite locally constant sheaves. -/
theorem etaleSetPullback_unit_finiteEtale_bijective_of_finiteEtaleFullyFaithful
    {X Y : Scheme.{u}} (i : Y ⟶ X)
    (hFE : (FiniteEtale.pullback i).FullyFaithful)
    {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsEtaleFiniteLocallyConstantSet F) (W : FiniteEtale X) :
    Function.Bijective
      (((etaleSetPullbackPushforwardAdjunction i).unit.app F).hom.app
          (op ((finiteEtaleToEtale X).obj W))) := by
  let P := etaleSetPullback i
  let adj := etaleSetPullbackPushforwardAdjunction i
  let U := (finiteEtaleToEtale X).obj W
  let T := X.smallEtaleTopology.yoneda.obj U
  have hmap : Function.Bijective (P.map : (T ⟶ F) → _) :=
    etaleSetPullback_map_bijective_of_finiteEtaleFullyFaithful i hFE
      (finiteEtaleSheaf_isEtaleFiniteLocallyConstantSet W) hF
  have hpost : Function.Bijective (fun a : T ⟶ F => a ≫ adj.unit.app F) := by
    have heq : (fun a : T ⟶ F => (adj.homEquiv T (P.obj F)) (P.map a)) =
        (fun a : T ⟶ F => a ≫ adj.unit.app F) := by
      funext a
      exact (adj.homEquiv_unit T (P.obj F) (P.map a)).trans
        (adj.unit.naturality a).symm
    rw [← heq]
    exact (adj.homEquiv T (P.obj F)).bijective.comp hmap
  let e₁ : (T ⟶ F) ≃ F.obj.obj (op U) := X.smallEtaleTopology.yonedaEquiv
  let e₂ : (T ⟶ (etaleSetPushforward i).obj (P.obj F)) ≃
      ((etaleSetPushforward i).obj (P.obj F)).obj.obj (op U) :=
    X.smallEtaleTopology.yonedaEquiv
  have heq : ((adj.unit.app F).hom.app (op U)) ∘ e₁ =
      e₂ ∘ (fun a : T ⟶ F => a ≫ adj.unit.app F) := by
    funext a
    exact (X.smallEtaleTopology.yonedaEquiv_comp a (adj.unit.app F)).symm
  apply (Function.Bijective.of_comp_iff _ e₁.bijective).mp
  rw [heq]
  exact e₂.bijective.comp hpost

/-- The actual closed-fibre adjunction unit is bijective on sections over
every finite étale object for finite locally constant coefficients. -/
theorem etaleSetClosedFiber_unit_finiteEtale_bijective
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsEtaleFiniteLocallyConstantSet F) (W : FiniteEtale X) :
    Function.Bijective
      (((etaleSetPullbackPushforwardAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).unit.app F).hom.app
          (op ((finiteEtaleToEtale X).obj W))) :=
  etaleSetPullback_unit_finiteEtale_bijective_of_finiteEtaleFullyFaithful _
    (FiniteEtale.pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing f) hF W

/-- In particular the actual closed-fibre unit is bijective on global
sections of every finite locally constant set sheaf. -/
theorem etaleSetClosedFiber_unit_globalSections_bijective
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsEtaleFiniteLocallyConstantSet F) :
    Function.Bijective
      (((etaleSetPullbackPushforwardAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).unit.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 X)))) :=
  etaleSetClosedFiber_unit_finiteEtale_bijective f hF
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (𝟙 X)
      (show IsFiniteEtale (𝟙 X) from ⟨⟩))

end EtaleCohomology
