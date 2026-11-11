/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CompletionColimitFamilySpecialization
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationValuation
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSpecifiedLift
public import Nyll.EtaleFundamentalGroups.GeometricFiber.NoetherianSpecializationExistence
public import Mathlib.Algebra.Ring.ULift

/-!
# Specialization existence over an arbitrary base scheme

The actual valuation family of the chosen geometric specialization has a
strict henselian local base. Its constructed completion colimit supplies
specialization, and the actual valuation-fiber comparisons transport that
map and its path to the original geometric fibers. The triangle remains
on the original total space. Only the two specified fibers need be
connected; no Noetherian condition is imposed on the original base.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory IsLocalRing AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- A chosen geometric specialization over an arbitrary base gives a
continuous map on the two connected geometric fibers, with constructed
geometric points, path, and the original total-space triangle. -/
theorem exists_familySpecialization_of_connectedFibers
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsAlgClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* kt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint ks)) t h).hom)
    (hgeneric : ConnectedSpace ↥(pullback t f))
    (hspecial : ConnectedSpace ↥(pullback s f)) :
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f)
      (τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, fundamentalGroupHom (pullback.snd s f) xs (sp a) =
        continuousConjAut τ (fundamentalGroupHom (pullback.snd t f) xη a) := by
  obtain ⟨V, hV, hVr, k, hk, hkc, j, o, α, _, _, _, hdata⟩ :=
    exists_valuationFamily_of_specializationLift f s t h ψ hψ
  let p := Spec.map (CommRingCat.ofHom α) ≫ localGeometricStalkToScheme s
  let g := pullback.fst p f
  let γ := Spec.map (CommRingCat.ofHom (algebraMap V kt))
  let δ := Spec.map (CommRingCat.ofHom (o.comp (residue V)))
  obtain ⟨qη, qs, _, _, hηtri, hηiso, _, hstri, _, _, hseq, _⟩ := hdata
  have : IsIso qη := hηiso
  have : (FiniteEtale.pullback qη).IsEquivalence :=
    (MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ (asIso qη).symm).isEquivalence_functor
  have : (FiniteEtale.pullback qs).IsEquivalence := hseq
  have hgenericV : ConnectedSpace ↥(pullback γ g) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qη).mpr hgeneric
  have hspecialV : ConnectedSpace ↥(pullback δ g) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qs).mpr hspecial
  let : Algebra (ULift.{u} ℤ) V :=
    ((algebraMap ℤ V).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  obtain ⟨Ωη, hΩη, hΩηc, Ωs, hΩs, hΩsc, xη, xs, τ, sp, hsp⟩ :=
    exists_completionColimitSpecialization_of_connectedFibers
      (ULift.{u} ℤ) V f p (algebraMap V kt) o hgenericV hspecialV
  let jη := pullback.snd γ g ≫ pullback.snd p f
  let js := pullback.snd δ g ≫ pullback.snd p f
  have hη' : qη ≫ pullback.snd t f = jη ≫ 𝟙 X :=
    hηtri.trans (Category.comp_id jη).symm
  have hs' : qs ≫ pullback.snd s f = js ≫ 𝟙 X :=
    hstri.trans (Category.comp_id js).symm
  obtain ⟨τ', sp', hsp'⟩ := transportSpecializationThroughFiberComparisons
    qη qs jη js (pullback.snd t f) (pullback.snd s f) (𝟙 X)
      hη' hs' xη xs τ sp hsp
  exact ⟨Ωη, hΩη, hΩηc, Ωs, hΩs, hΩsc, xη ≫ qη, xs ≫ qs, τ', sp', hsp'⟩

/-- A specialization with algebraically closed generic pointing field
supplies its own geometric lift. The base is arbitrary, and the actual
map, path and original total-space triangle are constructed. -/
theorem exists_familySpecialization_of_specializes_of_connectedFibers
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsAlgClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (hgeneric : ConnectedSpace ↥(pullback t f))
    (hspecial : ConnectedSpace ↥(pullback s f)) :
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f)
      (τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, fundamentalGroupHom (pullback.snd s f) xs (sp a) =
        continuousConjAut τ (fundamentalGroupHom (pullback.snd t f) xη a) := by
  obtain ⟨ψ, hψ, _⟩ := exists_localGeometricStalk_specifiedSpecializationLift s t h
  exact exists_familySpecialization_of_connectedFibers f s t h ψ hψ hgeneric hspecial

/-- An arbitrary-base specialization between arbitrary geometric pointing
fields gives an actual continuous specialization map, path, and original
total-space triangle. No geometric lift is supplied as an assumption. -/
theorem exists_generalFamilySpecialization_of_connectedFibers
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsSepClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (hgeneric : ConnectedSpace ↥(pullback t f))
    (hspecial : ConnectedSpace ↥(pullback s f)) :
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f)
      (τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, fundamentalGroupHom (pullback.snd s f) xs (sp a) =
        continuousConjAut τ (fundamentalGroupHom (pullback.snd t f) xη a) := by
  let K := AlgebraicClosure kt
  let ι : kt →+* K := algebraMap kt K
  let t' := Spec.map (CommRingCat.ofHom ι) ≫ t
  have ht' : t' (closedPoint K) = t (closedPoint kt) := by
    change t (Spec.map (CommRingCat.ofHom ι) (closedPoint K)) = t (closedPoint kt)
    exact congrArg t (Subsingleton.elim _ _)
  have h' : t' (closedPoint K) ⤳ s (closedPoint ks) := ht'.symm ▸ h
  have hid : f ≫ 𝟙 S = 𝟙 X ≫ f := by rw [Category.comp_id, Category.id_comp]
  have ht : t' ≫ 𝟙 S = Spec.map (CommRingCat.ofHom ι) ≫ t := Category.comp_id _
  have hcart : IsPullback (𝟙 X) f f (𝟙 S) := IsPullback.of_id_fst (f := f)
  let q := familyGeometricFiberMap f f (𝟙 X) (𝟙 S) hid t' t ι ht
  have : (FiniteEtale.pullback q).IsEquivalence :=
    pullback_familyGeometricFiberMap_isEquivalence f f (𝟙 X) (𝟙 S) hid t' t ι ht hcart
  have hgeneric' : ConnectedSpace ↥(pullback t' f) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence q).mpr hgeneric
  obtain ⟨Ωη, hΩη, hΩηc, Ωs, hΩs, hΩsc, xη, xs, τ, sp, hsp⟩ :=
    exists_familySpecialization_of_specializes_of_connectedFibers
      f s t' h' hgeneric' hspecial
  have hq : q ≫ pullback.snd t f = pullback.snd t' f ≫ 𝟙 X :=
    familyGeometricFiberMap_snd f f (𝟙 X) (𝟙 S) hid t' t ι ht
  have hs : (𝟙 (pullback s f)) ≫ pullback.snd s f = pullback.snd s f ≫ 𝟙 X := by
    rw [Category.id_comp, Category.comp_id]
  have : (FiniteEtale.pullback (𝟙 (pullback s f))).IsEquivalence :=
    (MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤
      (Iso.refl (pullback s f))).isEquivalence_functor
  obtain ⟨τ', sp', hsp'⟩ := transportSpecializationThroughFiberComparisons
    q (𝟙 (pullback s f)) (pullback.snd t' f) (pullback.snd s f)
    (pullback.snd t f) (pullback.snd s f) (𝟙 X) hq hs xη xs τ sp hsp
  exact ⟨Ωη, hΩη, hΩηc, Ωs, hΩs, hΩsc,
    xη ≫ q, xs ≫ 𝟙 (pullback s f), τ', sp', hsp'⟩

/-- Specialization over an arbitrary base at the originally supplied
geometric basepoints, assuming connectedness only of the two specified
fibers. The path and triangle refer to the original total space. -/
theorem exists_generalFamilySpecialization_at_points_of_connectedFibers
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsSepClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (hgeneric : ConnectedSpace ↥(pullback t f))
    (hspecial : ConnectedSpace ↥(pullback s f))
    {Ωη Ωs : Type u} [Field Ωη] [IsSepClosed Ωη] [Field Ωs] [IsSepClosed Ωs]
    (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f) :
    ∃ τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f),
      ∃ sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs), ∀ a,
        fundamentalGroupHom (pullback.snd s f) xs (sp a) =
          continuousConjAut τ (fundamentalGroupHom (pullback.snd t f) xη a) := by
  have : ConnectedSpace ↥(pullback t f) := hgeneric
  have : ConnectedSpace ↥(pullback s f) := hspecial
  obtain ⟨Ωη', hΩη', hΩηc', Ωs', hΩs', hΩsc', yη, ys, τ, sp, hsp⟩ :=
    exists_generalFamilySpecialization_of_connectedFibers f s t h hgeneric hspecial
  exact exists_specialization_at_geometric_basepoints
    (pullback.snd t f) (pullback.snd s f) yη ys xη xs τ sp hsp

end EtaleFundamentalGroups.StrictHenselian
