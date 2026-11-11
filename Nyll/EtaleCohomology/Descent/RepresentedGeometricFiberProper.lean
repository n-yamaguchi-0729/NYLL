/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberRestriction
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.RepresentedFiberEtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGeometricStalks
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionRepresentedBaseChange
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.SchemeTheory.Etale.ClosedNeighborhoodLift
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper represented geometric-fiber sections over any scheme base

A geometric point factors through an original affine chart. The existing
ordinary étale restriction and direct-image base-change isomorphisms,
with their original germ formulas, transfer the verified affine proper
comparison to the original arbitrary-base stalk map.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

/-- For a proper morphism over any scheme base, the original represented
direct-image geometric stalk is exactly the actual sections of each finite
étale representer over the original geometric fiber. -/
theorem etaleSetPushforwardRepresentableFiberSections_bijective
    {S Y : Scheme.{u}} (q : Y ⟶ S) [IsProper q]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ S) (V : FiniteEtale Y) :
    Function.Bijective (etaleSetPushforwardRepresentableFiberSections q t
      ((finiteEtaleToEtale Y).obj V)) := by
  obtain ⟨a, r, hr⟩ := AlgebraicGeometry.Etale.exists_affineCover_factor t
  let R : CommRingCat.{u} := S.affineOpenCover.X a
  let i : Spec R ⟶ S := S.affineOpenCover.f a
  have hi : IsOpenImmersion i := S.affineCover.map_prop a
  have hiEtale : Etale i := inferInstance
  change Spec (CommRingCat.of Ω) ⟶ Spec R at r
  change r ≫ i = t at hr
  subst t
  let P := pullback i q
  let p : P ⟶ Spec R := pullback.fst i q
  let g : P ⟶ Y := pullback.snd i q
  have hg : Etale g := inferInstanceAs (Etale (pullback.snd i q))
  have hp : IsProper p := inferInstanceAs (IsProper (pullback.fst i q))
  let H : IsPullback p g i q := IsPullback.of_hasPullback i q
  let W := (finiteEtaleToEtale Y).obj V
  let F := (etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)
  let Ψ := Scheme.pointSmallEtale r
  let E := (etaleRestrictionGeometricStalkIso i r (Type u) F).hom
  let B := Ψ.sheafFiber.map
    (etaleRestrictionPushforwardYonedaBaseChangeIso i q p g H W).hom
  let Cq := etaleSetPushforwardRepresentableFiberSections q (r ≫ i) W
  let Cp := etaleSetPushforwardRepresentableFiberSections p r ((etaleBaseChange g).obj W)
  let D := TypeCat.ofHom (representedFiberRestrictionEquiv i q p g H r W)
  have hCp : Function.Bijective Cp := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective r
    subst r
    exact etaleSetPushforwardRepresentableFiberSections_bijective_spec φ.hom p
      ((FiniteEtale.pullback g).obj V)
  have hE : Function.Bijective E := ConcreteCategory.bijective_of_isIso E
  have hB : Function.Bijective B := ConcreteCategory.bijective_of_isIso B
  have hD : Function.Bijective D :=
    (representedFiberRestrictionEquiv i q p g H r W).bijective
  have heq : E ≫ Cq ≫ D = B ≫ Cp :=
    etaleSetPushforwardRepresentableFiberSections_restriction i q p g H r W
  have hcomp : Function.Bijective (E ≫ Cq ≫ D) :=
    heq.symm ▸ hCp.comp hB
  apply (Function.Bijective.of_comp_iff' hD Cq).mp
  exact (Function.Bijective.of_comp_iff (D ∘ Cq) hE).mp hcomp

end EtaleCohomology
