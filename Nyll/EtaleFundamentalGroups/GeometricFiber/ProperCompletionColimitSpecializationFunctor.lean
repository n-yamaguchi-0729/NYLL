/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompletionColimitSpecialization
import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteGeometricSpecializationFunctor

/-!
# Cover specialization over the constructed completion colimit

The proved geometric closed-fiber equivalence over the constructed ring
supplies an actual specialization functor, its recovery on total-space
covers and its pointed fiber comparison. Morphisms of proper families
over this same constructed base give natural isomorphisms through the
original fiber maps. The original henselian ring need not be Noetherian.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

open HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]
  [IsSepClosed (IsLocalRing.ResidueField A)]
  {X : Scheme.{u}} (f : X ⟶ Spec (completionColimit R A)) [IsProper f]
  {k : Type u} [Field k] [IsSepClosed k]
  (s : Spec (CommRingCat.of k) ⟶ Spec (completionColimit R A))
  (ι : IsLocalRing.ResidueField (completionColimit R A) →+* k)
  (hs : s = Spec.map (CommRingCat.ofHom ι) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue (completionColimit R A))))

/-- The forward functor is the literal original geometric closed-fiber pullback. -/
def properCompletionColimitGeometricClosedFiberEquivalence :
    FiniteEtale X ≌ FiniteEtale (Limits.pullback f s) := by
  have : (pullback (Limits.pullback.fst f s)).IsEquivalence :=
    pullback_geometricClosedFiber_isEquivalence_completionColimit R A f s ι hs
  exact (pullback (Limits.pullback.fst f s)).asEquivalence

variable {K : Type u} [Field K]
  (η : Spec (CommRingCat.of K) ⟶ Spec (completionColimit R A))

/-- Lift a closed-fiber cover by the proved equivalence and restrict it to the chosen fiber. -/
def properCompletionColimitGeometricSpecializationFunctor :
    FiniteEtale (Limits.pullback f s) ⥤ FiniteEtale (Limits.pullback f η) :=
  (properCompletionColimitGeometricClosedFiberEquivalence R A f s ι hs).inverse ⋙
    pullback (Limits.pullback.fst f η)

/-- A total-space cover recovers its actual restriction to the chosen fiber. -/
def properCompletionColimitGeometricSpecializationFunctor_recovery :
    pullback (Limits.pullback.fst f s) ⋙
        properCompletionColimitGeometricSpecializationFunctor R A f s ι hs η ≅
      pullback (Limits.pullback.fst f η) :=
  (properCompletionColimitGeometricClosedFiberEquivalence R A f s ι hs).funInvIdAssoc
    (pullback (Limits.pullback.fst f η))

/-- The selected total-space path supplies the comparison on the specified geometric points. -/
def properCompletionColimitGeometricSpecializationFunctor_fiberIso
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (CommRingCat.of Ωη) ⟶ Limits.pullback f η)
    (xs : Spec (CommRingCat.of Ωs) ⟶ Limits.pullback f s)
    (t : fiber (xη ≫ Limits.pullback.fst f η) ≅
      fiber (xs ≫ Limits.pullback.fst f s)) :
    properCompletionColimitGeometricSpecializationFunctor R A f s ι hs η ⋙ fiber xη ≅
      fiber xs :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (properCompletionColimitGeometricClosedFiberEquivalence R A f s ι hs).inverse
      (pullbackFiberIso (Limits.pullback.fst f η) xη ≪≫ t ≪≫
        (pullbackFiberIso (Limits.pullback.fst f s) xs).symm) ≪≫
    (properCompletionColimitGeometricClosedFiberEquivalence R A f s ι hs).invFunIdAssoc
      (fiber xs)

/-- Morphisms of proper families over the same constructed base commute
with specialization through their actual closed and generic fiber maps. -/
def properCompletionColimitGeometricSpecializationFunctor_naturality
    {Y : Scheme.{u}} (g : Y ⟶ Spec (completionColimit R A)) [IsProper g]
    (a : X ⟶ Y) (ha : a ≫ g = f) :
    pullback (properFamilyFiberMap f g a ha s) ⋙
        properCompletionColimitGeometricSpecializationFunctor R A f s ι hs η ≅
      properCompletionColimitGeometricSpecializationFunctor R A g s ι hs η ⋙
        pullback (properFamilyFiberMap f g a ha η) := by
  let E := properCompletionColimitGeometricClosedFiberEquivalence R A f s ι hs
  let F := properCompletionColimitGeometricClosedFiberEquivalence R A g s ι hs
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
