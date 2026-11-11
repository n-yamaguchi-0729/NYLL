/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FaithfullyFlat
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveOverCompletion
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientSequence
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.ReductionSystemComparison
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Flatness of a finite module detected by its actual adic reductions

Reuse the constructed projective module over the coefficient completion
and the original reduction-system comparison. Faithfully flat descent
then gives flatness of the original module. Over a Noetherian local ring,
maximal-ideal completion supplies faithful flatness, so the actual finite
module is free whenever all its positive infinitesimal reductions are flat.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u

namespace AdicModuleSystem

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (I : Ideal R) (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P]

/-- The already constructed completion comparison descends flatness from
projective adic reductions along a faithfully flat coefficient completion. -/
theorem flat_of_projective_reductions_of_faithfullyFlat_completion
    [Module.FaithfullyFlat R (AdicCompletion I R)]
    (hproj : ∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1))
      (P ⧸ (I ^ (n + 1) • (⊤ : Submodule R P)))) : Module.Flat R P := by
  let Q : ℕ → Type u := fun n => P ⧸ (I ^ (n + 1) • (⊤ : Submodule R P))
  let δ : ∀ n : ℕ, Q (n + 1) →ₗ[R] Q n := quotientSequenceTransition I P
  let η : ∀ n : ℕ, P →ₗ[R] Q n := fun n =>
    (I ^ (n + 1) • (⊤ : Submodule R P)).mkQ
  have hη : ∀ n : ℕ, (δ n).comp (η (n + 1)) = η n := by
    intro n
    apply LinearMap.ext
    intro x
    rfl
  have hηsurj : ∀ n : ℕ, Function.Surjective (η n) := fun n =>
    Submodule.mkQ_surjective _
  have hηker : ∀ n : ℕ, (η n).ker = I ^ (n + 1) • (⊤ : Submodule R P) :=
    fun n => Submodule.ker_mkQ _
  have hprojQ : ∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1)) (Q n) := hproj
  have hcompleted : Module.Projective (AdicCompletion I R)
      (sections (fun n => AdicCompletion I (Q n))
        (fun n => AdicCompletion.map I (δ n))) :=
    completed_sections_projective (fun n => Q n) δ I
      (quotientSequenceModule_annihilated I P)
      (quotientSequenceTransition_surjective I P) (quotientSequenceTransition_ker I P)
  let e : AdicCompletion I P ≃ₗ[AdicCompletion I R]
      sections (fun n => AdicCompletion I (Q n))
        (fun n => AdicCompletion.map I (δ n)) :=
    LinearEquiv.ofBijective (completedReductionSectionsMap I (fun n => Q n) δ η hη)
      (completedReductionSectionsMap_bijective I (fun n => Q n) δ η hη
        hηsurj hηker (IsNoetherian.noetherian I))
  have : Module.Projective (AdicCompletion I R) (AdicCompletion I P) :=
    Module.Projective.of_equiv' e.symm
  have : Module.Flat (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] P) :=
    Module.Flat.of_linearEquiv
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I P)
  exact Module.Flat.of_flat_tensorProduct R P (AdicCompletion I R)

end AdicModuleSystem

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Completion along any proper ideal of a Noetherian local ring is
faithfully flat, using the existing maximal-ideal extension criterion. -/
theorem faithfullyFlat_adicCompletion_of_ne_top (I : Ideal R) (hI : I ≠ ⊤) :
    Module.FaithfullyFlat R (AdicCompletion I R) := by
  have hflat : Module.Flat R (AdicCompletion I R) :=
    AdicCompletion.flat_of_isNoetherian I
  have hm : ((maximalIdeal R).map (algebraMap R (AdicCompletion I R))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I (maximalIdeal R)
      (le_maximalIdeal hI) (IsNoetherian.noetherian I)
  apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal R _).mpr
  refine ⟨hflat, ?_⟩
  intro J hJ htop
  have hle : J • (⊤ : Submodule R (AdicCompletion I R)) ≤
      maximalIdeal R • (⊤ : Submodule R (AdicCompletion I R)) :=
    Submodule.smul_mono_left (le_maximalIdeal hJ)
  rw [htop, top_le_iff, Ideal.smul_top_eq_map] at hle
  exact hm.ne_top ((Submodule.restrictScalars_eq_top_iff R _ _).mp hle)

/-- Flat reductions along any proper ideal force a finite module over a
Noetherian local ring to be free. The original ring need not be complete. -/
theorem free_of_flat_reductions_of_ne_top (I : Ideal R) (hI : I ≠ ⊤)
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ I ^ (n + 1))
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) : Module.Free R M := by
  have hfaithful : Module.FaithfullyFlat R (AdicCompletion I R) :=
    faithfullyFlat_adicCompletion_of_ne_top I hI
  have hprojective (n : ℕ) : Module.Projective (R ⧸ I ^ (n + 1))
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := by
    have : Module.Flat (R ⧸ I ^ (n + 1))
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := hflat n
    have : Module.Finite (R ⧸ I ^ (n + 1))
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have : Module.FinitePresentation (R ⧸ I ^ (n + 1))
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) :=
      Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  have : Module.Flat R M :=
    AdicModuleSystem.flat_of_projective_reductions_of_faithfullyFlat_completion
      I M hprojective
  exact Module.free_of_flat_of_isLocalRing

/-- All positive maximal-ideal reductions being flat forces the original
finite local module to be free. -/
theorem free_of_flat_adic_reductions
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ maximalIdeal R ^ (n + 1))
      (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M)))) : Module.Free R M :=
  free_of_flat_reductions_of_ne_top M (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top hflat

end IsLocalRing
