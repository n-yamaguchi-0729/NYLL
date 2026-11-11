/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CompletionColimitFamilyComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.DVRCompletionSpecialization

/-!
# Specialization from the actual completion-colimit family

The constructed geometric-fiber comparisons transfer connectedness of the
two specified fibers. The proved closed-fiber equivalence then supplies
connectedness of the constructed total space. Actual geometric points,
a path, and the inverse of that equivalence give a continuous specialization
map. Transport through the actual fiber comparisons retains the original
total-space triangle. The original henselian base need not be Noetherian.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory IsLocalRing
open AlgebraicGeometry.HenselianNoetherianImageStages AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Two specified connected geometric fibers suffice for specialization
over an arbitrary strict henselian local base. The map, geometric points,
path, and triangle to the original total space are constructed. -/
theorem exists_completionColimitSpecialization_of_connectedFibers
    (R A : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (p : Spec (CommRingCat.of A) ⟶ S)
    {K k : Type u} [Field K] [IsSepClosed K] [Field k] [IsSepClosed k]
    (ψ : A →+* K) (o : ResidueField A →+* k)
    (hgeneric : ConnectedSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom ψ)) (pullback.fst p f)))
    (hspecial : ConnectedSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom (o.comp (residue A)))) (pullback.fst p f))) :
    let g := pullback.fst p f
    let γ := Spec.map (CommRingCat.ofHom ψ)
    let δ := Spec.map (CommRingCat.ofHom (o.comp (residue A)))
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback γ g) (xs : Spec (.of Ωs) ⟶ pullback δ g)
      (τ : FiniteEtale.fiber (xη ≫ (pullback.snd γ g ≫ pullback.snd p f)) ≅
        FiniteEtale.fiber (xs ≫ (pullback.snd δ g ≫ pullback.snd p f)))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, fundamentalGroupHom (pullback.snd δ g ≫ pullback.snd p f) xs (sp a) =
        continuousConjAut τ
          (fundamentalGroupHom (pullback.snd γ g ≫ pullback.snd p f) xη a) := by
  intro g γ δ
  obtain ⟨L, hL, hLc, β, α, _, hdata⟩ :=
    exists_completionColimitFamilyComparison R A f p ψ o
  let q := Spec.map (completionBaseMap R A)
  let ĝ := pullback.fst q g
  let γ' := Spec.map (CommRingCat.ofHom α)
  let o' := o.comp (completionResidueEquiv R A).toRingHom
  let δ' := Spec.map (CommRingCat.ofHom (o'.comp (residue (completionColimit R A))))
  obtain ⟨qη, qs, _, hηtri, _, hstri, hηeq, hseq, hcleq, _⟩ := hdata
  have : (FiniteEtale.pullback qη).IsEquivalence := hηeq
  have : (FiniteEtale.pullback qs).IsEquivalence := hseq
  have : (FiniteEtale.pullback (pullback.snd δ' ĝ)).IsEquivalence := hcleq
  have : ConnectedSpace ↥(pullback γ' ĝ) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qη).mpr hgeneric
  have : ConnectedSpace ↥(pullback δ' ĝ) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qs).mpr hspecial
  have : ConnectedSpace ↥(pullback q g) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence (pullback.snd δ' ĝ)).mp
      inferInstance
  let yη : ↥(pullback γ' ĝ) := Classical.choice (inferInstance : Nonempty ↥(pullback γ' ĝ))
  let ys : ↥(pullback δ' ĝ) := Classical.choice (inferInstance : Nonempty ↥(pullback δ' ĝ))
  let Ωη := AlgebraicClosure ((pullback γ' ĝ).residueField yη)
  let Ωs := AlgebraicClosure ((pullback δ' ĝ).residueField ys)
  let xη : Spec (.of Ωη) ⟶ pullback γ' ĝ :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((pullback γ' ĝ).residueField yη) Ωη)) ≫
        (pullback γ' ĝ).fromSpecResidueField yη
  let xs : Spec (.of Ωs) ⟶ pullback δ' ĝ :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((pullback δ' ĝ).residueField ys) Ωs)) ≫
        (pullback δ' ĝ).fromSpecResidueField ys
  obtain ⟨τ⟩ := nonempty_fiber_iso (xη ≫ pullback.snd γ' ĝ) (xs ≫ pullback.snd δ' ĝ)
  let ej : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xs ≫ pullback.snd δ' ĝ) :=
    autEquivOfCompIsoOfEquivalence (FiniteEtale.pullback (pullback.snd δ' ĝ))
      (pullbackFiberIso (pullback.snd δ' ĝ) xs)
  let spC : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs) :=
    (ContinuousMonoidHom.toContinuousMonoidHom ej.symm).comp
      ((ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut τ)).comp
        (fundamentalGroupHom (pullback.snd γ' ĝ) xη))
  have hC (a : π₁ᵉᵗ(xη)) :
      fundamentalGroupHom (pullback.snd δ' ĝ) xs (spC a) =
        continuousConjAut τ (fundamentalGroupHom (pullback.snd γ' ĝ) xη a) := by
    change ej (ej.symm (continuousConjAut τ (fundamentalGroupHom (pullback.snd γ' ĝ) xη a))) = _
    exact ej.apply_symm_apply _
  obtain ⟨τOld, sp, hsp⟩ := transportSpecializationThroughFiberComparisons
    qη qs (pullback.snd γ' ĝ) (pullback.snd δ' ĝ)
    (pullback.snd γ g ≫ pullback.snd p f) (pullback.snd δ g ≫ pullback.snd p f)
    (pullback.snd q g ≫ pullback.snd p f) hηtri hstri xη xs τ spC hC
  exact ⟨Ωη, inferInstance, inferInstance, Ωs, inferInstance, inferInstance,
    xη ≫ qη, xs ≫ qs, τOld, sp, hsp⟩

end EtaleFundamentalGroups.StrictHenselian
