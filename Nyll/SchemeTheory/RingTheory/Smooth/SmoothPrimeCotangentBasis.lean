/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Selecting original relation classes at a smooth prime

The original polynomial presentation is retained. Smoothness of its target
localization splits the localized cotangent sequence, so its localized
conormal module is projective. At a prime it is free, with a finite basis
selected from the images of the original relations.
-/

@[expose] public section

noncomputable section

universe u v w t

open scoped TensorProduct

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- Smoothness after localization splits the original cotangent sequence. -/
theorem Generators.exists_retraction_baseChangeCotangent_of_formallySmooth_localization
    {ι : Type w} (P : Generators R B ι) (M : Submonoid B)
    (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    [Algebra R T] [IsScalarTower R B T] [FormallySmooth R T] :
    ∃ l : (T ⊗[B] P.toExtension.CotangentSpace) →ₗ[T]
      T ⊗[B] P.toExtension.Cotangent,
      l.comp (P.toExtension.cotangentComplex.baseChange T) = LinearMap.id := by
  have : Module.Flat B T := IsLocalization.flat T M
  have : FormallyEtale B T := FormallyEtale.of_isLocalization M
  let eH : (T ⊗[B] P.toExtension.H1Cotangent) ≃ₗ[T] H1Cotangent R T :=
    (P.equivH1Cotangent.baseChange B T _ _).trans
      (tensorH1CotangentOfIsLocalization R T M)
  have : Subsingleton (T ⊗[B] P.toExtension.H1Cotangent) := eH.toEquiv.subsingleton
  let d : (T ⊗[B] P.toExtension.Cotangent) →ₗ[T]
      T ⊗[B] P.toExtension.CotangentSpace :=
    P.toExtension.cotangentComplex.baseChange T
  let q : (T ⊗[B] P.toExtension.CotangentSpace) →ₗ[T]
      T ⊗[B] KaehlerDifferential R B := P.toExtension.toKaehler.baseChange T
  have hd : Function.Injective d := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hExact : Function.Exact (P.toExtension.h1Cotangentι.baseChange T) d :=
      Module.Flat.lTensor_exact T P.toExtension.exact_hCotangentι_cotangentComplex
    obtain ⟨y, hy⟩ := (hExact x).mp hx
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  have hExact : Function.Exact d q :=
    Module.Flat.lTensor_exact T P.toExtension.exact_cotangentComplex_toKaehler
  have hq : Function.Surjective q :=
    LinearMap.baseChange_surjective T P.toExtension.toKaehler_surjective
  have : Module.Projective T (T ⊗[B] KaehlerDifferential R B) :=
    Module.Projective.of_equiv
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B T).symm
  have hsection : ∃ s : (T ⊗[B] KaehlerDifferential R B) →ₗ[T]
      T ⊗[B] P.toExtension.CotangentSpace, q.comp s = LinearMap.id :=
    Module.projective_lifting_property q LinearMap.id hq
  have hsplit : (Function.Injective d ∧
      ∃ s : (T ⊗[B] KaehlerDifferential R B) →ₗ[T]
        T ⊗[B] P.toExtension.CotangentSpace, q.comp s = LinearMap.id) ↔
      (Function.Surjective q ∧
        ∃ l : (T ⊗[B] P.toExtension.CotangentSpace) →ₗ[T]
          T ⊗[B] P.toExtension.Cotangent, l.comp d = LinearMap.id) :=
    hExact.split_tfae'.out 1 2 rfl rfl
  exact (hsplit.mp ⟨hd, hsection⟩).2

/-- Smoothness after localization makes the base change of the original
presentation's conormal module projective. -/
theorem Generators.projective_baseChangeCotangent_of_formallySmooth_localization
    {ι : Type w} (P : Generators R B ι) (M : Submonoid B)
    (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    [Algebra R T] [IsScalarTower R B T] [FormallySmooth R T] :
    Module.Projective T (T ⊗[B] P.toExtension.Cotangent) := by
  obtain ⟨l, hl⟩ := P.exists_retraction_baseChangeCotangent_of_formallySmooth_localization M T
  have : Module.Free T (T ⊗[B] P.toExtension.CotangentSpace) :=
    Module.Free.of_basis (P.cotangentSpaceBasis.baseChange T)
  exact Module.Projective.of_split (P.toExtension.cotangentComplex.baseChange T) l hl

private theorem exists_finite_basis_of_baseChange_span
    {T : Type*} [CommRing T] [Algebra B T] [IsLocalRing T]
    {N : Type*} [AddCommGroup N] [Module B N]
    [Module.Projective T (T ⊗[B] N)]
    {σ : Type t} [Finite σ] (v : σ → N)
    (hv : Submodule.span B (Set.range v) = ⊤) :
    ∃ (κ : Type t) (_ : Fintype κ) (a : κ → σ)
      (b : Module.Basis κ T (T ⊗[B] N)), ∀ i, b i = (1 : T) ⊗ₜ[B] v (a i) := by
  have : Module.Finite B N := Module.finite_def.mpr
    (hv ▸ Submodule.fg_span (Set.finite_range v))
  have hlocal : Submodule.span T (Set.range (fun j => (1 : T) ⊗ₜ[B] v j)) = ⊤ := by
    have h := congrArg (fun K : Submodule B N => K.baseChange T) hv
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top,
      ← Set.range_comp, Function.comp_def, TensorProduct.mk_apply] using h
  have : Module.FinitePresentation T (T ⊗[B] N) :=
    Module.finitePresentation_of_projective _ _
  obtain ⟨κ, a, b, hb⟩ :=
    Module.exists_basis_of_span_of_flat (fun j => (1 : T) ⊗ₜ[B] v j) hlocal
  have : Finite κ := Module.Finite.finite_basis b
  exact ⟨κ, Fintype.ofFinite κ, a, b, hb⟩

/-- At a smooth prime, a finite subfamily of the original relations is a
basis of the original conormal module after localization. -/
theorem Presentation.exists_finite_cotangentBasis_at_smoothPrime
    {ι : Type w} {σ : Type t} [Finite σ] (P : Presentation R B ι σ)
    (p : Ideal B) [p.IsPrime] [IsSmoothAt R p] :
    ∃ (κ : Type t) (_ : Fintype κ) (a : κ → σ)
      (b : Module.Basis κ (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[B] P.toExtension.Cotangent)),
      ∀ i, b i = (1 : Localization.AtPrime p) ⊗ₜ[B]
        Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (a i), P.relation_mem_ker (a i)⟩ := by
  let v : σ → P.toExtension.Cotangent := fun j =>
    Extension.Cotangent.mk (P := P.toExtension) ⟨P.relation j, P.relation_mem_ker j⟩
  have hv : Submodule.span B (Set.range v) = ⊤ :=
    Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P.toExtension)
      P.relation P.span_range_relation_eq_ker
  have : Module.Projective (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[B] P.toExtension.Cotangent) :=
    P.toGenerators.projective_baseChangeCotangent_of_formallySmooth_localization
      p.primeCompl (Localization.AtPrime p)
  exact exists_finite_basis_of_baseChange_span (T := Localization.AtPrime p) v hv

end Algebra
