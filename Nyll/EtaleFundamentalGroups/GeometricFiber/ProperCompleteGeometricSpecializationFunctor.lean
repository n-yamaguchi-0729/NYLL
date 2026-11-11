/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteGeometricSpecialization
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition

/-!
# The actual specialization functor over a complete strict local base

The proved geometric closed-fiber equivalence lifts covers to the original
proper total space, and pullback restricts them to the chosen generic
fiber. A morphism of the original families gives a natural isomorphism
between the two specialization functors through their actual fiber maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- The map on the actual fibers of a morphism over the same base. -/
def properFamilyFiberMap {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) (v : T ⟶ S) :
    Limits.pullback f v ⟶ Limits.pullback g v :=
  Limits.pullback.lift (Limits.pullback.fst f v ≫ a) (Limits.pullback.snd f v)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => Limits.pullback.fst f v ≫ q) ha).trans
        Limits.pullback.condition))

@[reassoc]
theorem properFamilyFiberMap_fst {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) (v : T ⟶ S) :
    properFamilyFiberMap f g a ha v ≫ Limits.pullback.fst g v =
      Limits.pullback.fst f v ≫ a :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem properFamilyFiberMap_snd {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) (v : T ⟶ S) :
    properFamilyFiberMap f g a ha v ≫ Limits.pullback.snd g v =
      Limits.pullback.snd f v :=
  Limits.pullback.lift_snd _ _ _

/-- The pullback square uses the original fiber projections and family map. -/
def properFamilyFiberPullbackIso {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) (v : T ⟶ S) :
    pullback a ⋙ pullback (Limits.pullback.fst f v) ≅
      pullback (Limits.pullback.fst g v) ⋙ pullback (properFamilyFiberMap f g a ha v) :=
  (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (Limits.pullback.fst f v) a).symm ≪≫
  MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (properFamilyFiberMap f g a ha v) (Limits.pullback.fst g v)
    (Limits.pullback.fst f v ≫ a) (properFamilyFiberMap_fst f g a ha v).symm

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  {k : Type u} [Field k] [IsSepClosed k]
  (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  (ι : IsLocalRing.ResidueField R →+* k)
  (hs : s = Spec.map (CommRingCat.ofHom ι) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))

/-- The proved comparison, with literally the geometric closed-fiber
pullback as its forward functor. -/
def properCompleteGeometricClosedFiberEquivalence :
    FiniteEtale X ≌ FiniteEtale (Limits.pullback f s) := by
  have : (pullback (Limits.pullback.fst f s)).IsEquivalence :=
    pullback_geometricClosedFiber_isEquivalence_of_isAdicComplete R f s ι hs
  exact (pullback (Limits.pullback.fst f s)).asEquivalence

variable {K : Type u} [Field K]
  (η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))

/-- Specialize a closed-fiber cover by its actual proper lift and generic
restriction. The chosen inverse is the inverse of the proved equivalence. -/
def properCompleteGeometricSpecializationFunctor :
    FiniteEtale (Limits.pullback f s) ⥤ FiniteEtale (Limits.pullback f η) :=
  (properCompleteGeometricClosedFiberEquivalence R f s ι hs).inverse ⋙
    pullback (Limits.pullback.fst f η)

/-- A cover already on the original total space specializes to its actual
generic restriction, with the unit of the same closed-fiber equivalence. -/
def properCompleteGeometricSpecializationFunctor_recovery :
    pullback (Limits.pullback.fst f s) ⋙
        properCompleteGeometricSpecializationFunctor R f s ι hs η ≅
      pullback (Limits.pullback.fst f η) :=
  (properCompleteGeometricClosedFiberEquivalence R f s ι hs).funInvIdAssoc
    (pullback (Limits.pullback.fst f η))

/-- The selected original total-space path gives the actual comparison of
fibers of the specialization functor at the selected geometric points. -/
def properCompleteGeometricSpecializationFunctor_fiberIso
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (CommRingCat.of Ωη) ⟶ Limits.pullback f η)
    (xs : Spec (CommRingCat.of Ωs) ⟶ Limits.pullback f s)
    (t : fiber (xη ≫ Limits.pullback.fst f η) ≅
      fiber (xs ≫ Limits.pullback.fst f s)) :
    properCompleteGeometricSpecializationFunctor R f s ι hs η ⋙ fiber xη ≅ fiber xs :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (properCompleteGeometricClosedFiberEquivalence R f s ι hs).inverse
      (pullbackFiberIso (Limits.pullback.fst f η) xη ≪≫ t ≪≫
        (pullbackFiberIso (Limits.pullback.fst f s) xs).symm) ≪≫
    (properCompleteGeometricClosedFiberEquivalence R f s ι hs).invFunIdAssoc (fiber xs)

/-- A morphism of the original proper families commutes with the actual
specialization functors through the actual maps of their two fibers. -/
def properCompleteGeometricSpecializationFunctor_naturality
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) [IsProper g]
    (a : X ⟶ Y) (ha : a ≫ g = f) :
    pullback (properFamilyFiberMap f g a ha s) ⋙
        properCompleteGeometricSpecializationFunctor R f s ι hs η ≅
      properCompleteGeometricSpecializationFunctor R g s ι hs η ⋙
        pullback (properFamilyFiberMap f g a ha η) := by
  let E := properCompleteGeometricClosedFiberEquivalence R f s ι hs
  let F := properCompleteGeometricClosedFiberEquivalence R g s ι hs
  let H := pullback a
  let J := pullback (properFamilyFiberMap f g a ha s)
  let P := pullback (Limits.pullback.fst f η)
  let Q := pullback (Limits.pullback.fst g η)
  let L := pullback (properFamilyFiberMap f g a ha η)
  let c : H ⋙ E.functor ≅ F.functor ⋙ J :=
    properFamilyFiberPullbackIso f g a ha s
  let d : (F.inverse ⋙ H) ⋙ E.functor ≅ J :=
    Functor.associator F.inverse H E.functor ≪≫ c.inverseCompIso (G := F)
  let b : J ⋙ E.inverse ≅ F.inverse ⋙ H := (d.isoCompInverse (H := E)).symm
  change J ⋙ (E.inverse ⋙ P) ≅ (F.inverse ⋙ Q) ⋙ L
  exact (Functor.associator J E.inverse P).symm ≪≫
    Functor.isoWhiskerRight b P ≪≫ Functor.associator F.inverse H P ≪≫
    Functor.isoWhiskerLeft F.inverse (properFamilyFiberPullbackIso f g a ha η) ≪≫
    (Functor.associator F.inverse Q L).symm

end AlgebraicGeometry.FiniteEtale
