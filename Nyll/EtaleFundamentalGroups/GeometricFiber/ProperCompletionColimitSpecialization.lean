/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperCompletionColimitFiniteEtale
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperFieldBaseChange
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ConnectedComponents
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Nyll.EtaleFundamentalGroups.GaloisCategories.EquivalenceFunctoriality

/-!
# Geometric specialization over the constructed completion colimit

The actual proper closed-fiber comparison over the constructed local ring
supplies specialization and its original total-space triangle. The initial
henselian ring is arbitrary, without a Noetherian hypothesis. Its original
residue field is retained by the proved native residue isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

open HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]
  [IsSepClosed (IsLocalRing.ResidueField A)]

/-- The constructed ring retains the separably closed original residue field. -/
instance completionColimit_residue_isSepClosed :
    IsSepClosed (IsLocalRing.ResidueField (completionColimit R A)) := by
  let e := completionResidueEquiv R A
  refine ⟨fun p hp => ?_⟩
  have h := (IsSepClosed.splits_of_separable (p.map e.toRingHom) hp.map).map e.symm.toRingHom
  simpa only [Polynomial.map_map, RingEquiv.symm_toRingHom_comp_toRingHom,
    Polynomial.map_id] using h

variable {X : Scheme.{u}} (f : X ⟶ Spec (completionColimit R A)) [IsProper f]
  {k : Type u} [Field k] [IsSepClosed k]
  (s : Spec (CommRingCat.of k) ⟶ Spec (completionColimit R A))
  (ι : IsLocalRing.ResidueField (completionColimit R A) →+* k)
  (hs : s = Spec.map (CommRingCat.ofHom ι) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue (completionColimit R A))))

include ι hs

/-- The actual geometric closed-fiber projection induces an equivalence;
the specified pointing field need not equal the residue field. -/
theorem pullback_geometricClosedFiber_isEquivalence_completionColimit :
    (pullback (Limits.pullback.fst f s)).IsEquivalence := by
  let ρ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue (completionColimit R A)))
  let q := fieldBaseChangeMap f ρ s ι hs
  have : (pullback q).IsEquivalence :=
    pullback_fieldBaseChangeMap_isEquivalence f ρ s ι hs
  have : (pullback (Limits.pullback.fst f ρ)).IsEquivalence :=
    pullback_isEquivalence_closedFiber_completionColimit R A f
  let c : pullback (Limits.pullback.fst f s) ≅
      pullback (Limits.pullback.fst f ρ) ⋙ pullback q :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      q (Limits.pullback.fst f ρ) (Limits.pullback.fst f s)
      (fieldBaseChangeMap_fst f ρ s ι hs).symm
  exact Functor.isEquivalence_of_iso c.symm

/-- The geometric closed-fiber comparison has the original projection as
its forward homomorphism. -/
def fundamentalGroupEquivProperCompletionColimitGeometricClosedFiber
    {Ω : Type u} [Field Ω]
    (xs : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f s) :
    π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xs ≫ Limits.pullback.fst f s) := by
  have : (pullback (Limits.pullback.fst f s)).IsEquivalence :=
    pullback_geometricClosedFiber_isEquivalence_completionColimit R A f s ι hs
  exact CategoryTheory.PreGaloisCategory.autEquivOfCompIsoOfEquivalence
    (pullback (Limits.pullback.fst f s))
    (pullbackFiberIso (Limits.pullback.fst f s) xs)

/-- Its forward map is literally induced by the geometric-fiber projection. -/
theorem fundamentalGroupEquivProperCompletionColimitGeometricClosedFiber_apply
    {Ω : Type u} [Field Ω]
    (xs : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f s) (a : π₁ᵉᵗ(xs)) :
    fundamentalGroupEquivProperCompletionColimitGeometricClosedFiber R A f s ι hs xs a =
      fundamentalGroupHom (Limits.pullback.fst f s) xs a := rfl

variable {K Ωη Ωs : Type u} [Field K] [Field Ωη] [Field Ωs]
  (η : Spec (CommRingCat.of K) ⟶ Spec (completionColimit R A))
  (xη : Spec (CommRingCat.of Ωη) ⟶ Limits.pullback f η)
  (xs : Spec (CommRingCat.of Ωs) ⟶ Limits.pullback f s)
  (t : fiber (xη ≫ Limits.pullback.fst f η) ≅
    fiber (xs ≫ Limits.pullback.fst f s))

/-- Specialization from the given geometric fiber to the given geometric
closed fiber, retaining both original fiber products and the chosen path. -/
def properCompletionColimitGeometricSpecializationHom : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (fundamentalGroupEquivProperCompletionColimitGeometricClosedFiber R A f s ι hs xs).symm).comp
      ((ContinuousMonoidHom.toContinuousMonoidHom
        (CategoryTheory.PreGaloisCategory.continuousConjAut t)).comp
          (fundamentalGroupHom (Limits.pullback.fst f η) xη))

/-- The specialization satisfies the total-space triangle for the actual
geometric-fiber projections and the selected path. -/
theorem properCompletionColimitGeometricSpecializationHom_triangle (a : π₁ᵉᵗ(xη)) :
    fundamentalGroupHom (Limits.pullback.fst f s) xs
        (properCompletionColimitGeometricSpecializationHom R A f s ι hs η xη xs t a) =
      CategoryTheory.PreGaloisCategory.continuousConjAut t
        (fundamentalGroupHom (Limits.pullback.fst f η) xη a) := by
  let e := fundamentalGroupEquivProperCompletionColimitGeometricClosedFiber R A f s ι hs xs
  change e (e.symm (CategoryTheory.PreGaloisCategory.continuousConjAut t
    (fundamentalGroupHom (Limits.pullback.fst f η) xη a))) = _
  exact e.apply_symm_apply _

/-- For a fixed path the total-space triangle determines specialization
uniquely, so no second choice of inverse can change the map. -/
theorem properCompletionColimitGeometricSpecializationHom_unique
    (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs))
    (hsp : ∀ a, fundamentalGroupHom (Limits.pullback.fst f s) xs (sp a) =
      CategoryTheory.PreGaloisCategory.continuousConjAut t
        (fundamentalGroupHom (Limits.pullback.fst f η) xη a)) :
    sp = properCompletionColimitGeometricSpecializationHom R A f s ι hs η xη xs t := by
  apply ContinuousMonoidHom.ext
  intro a
  apply (fundamentalGroupEquivProperCompletionColimitGeometricClosedFiber R A f s ι hs xs).injective
  exact (hsp a).trans
    (properCompletionColimitGeometricSpecializationHom_triangle R A f s ι hs η xη xs t a).symm

/-- Geometrically connected fibers supply connectedness of the total space
and the path between the given points, without extra existence hypotheses. -/
theorem exists_properCompletionColimitGeometricSpecializationHom
    [GeometricallyConnected f] [IsSepClosed Ωη] [IsSepClosed Ωs] :
    ∃ t : fiber (xη ≫ Limits.pullback.fst f η) ≅
        fiber (xs ≫ Limits.pullback.fst f s),
      ∃ sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs), ∀ a,
        fundamentalGroupHom (Limits.pullback.fst f s) xs (sp a) =
          CategoryTheory.PreGaloisCategory.continuousConjAut t
            (fundamentalGroupHom (Limits.pullback.fst f η) xη a) := by
  have : ConnectedSpace ↥(Limits.pullback f s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.snd f s)
  have : (pullback (Limits.pullback.fst f s)).IsEquivalence :=
    pullback_geometricClosedFiber_isEquivalence_completionColimit R A f s ι hs
  have : ConnectedSpace X :=
    (connectedSpace_iff_of_pullback_isEquivalence (Limits.pullback.fst f s)).mp inferInstance
  obtain ⟨t⟩ := nonempty_fiber_iso
    (xη ≫ Limits.pullback.fst f η) (xs ≫ Limits.pullback.fst f s)
  exact ⟨t, properCompletionColimitGeometricSpecializationHom R A f s ι hs η xη xs t,
    properCompletionColimitGeometricSpecializationHom_triangle R A f s ι hs η xη xs t⟩

end AlgebraicGeometry.FiniteEtale
