/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.LocalStandardSmoothFactorization
public import Nyll.SchemeTheory.RingTheory.Smooth.SquareZeroIndSmoothReduction
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Nilpotent smooth factorization into a local target

For a local target, every supplied smooth stage modulo a nilpotent
base ideal can be replaced by an actual standard smooth principal
localization. Applying the nilpotent relation-removal construction
then gives an exact smooth factorization over the original base.

This uses the original smooth factorization hypothesis, without a
standard-smooth strengthening, in the local-target case of Stacks
Project, Lemma 16.5.3:
https://stacks.math.columbia.edu/tag/07CM
-/

@[expose] public section

noncomputable section

universe u v

namespace Algebra

/-- For a flat local target, smooth factorization modulo a nilpotent
base ideal lifts to smooth factorization over the original base. -/
theorem exists_smooth_factorization_of_nilpotent_modulo_smooth_local
    {R : Type u} {L : Type v}
    [CommRing R] [CommRing L] [Algebra R L] [Module.Flat R L] [IsLocalRing L]
    (I : Ideal R) (hI : IsNilpotent I)
    (hmod : ∀ (A₀ : Type u) [CommRing A₀] [Algebra (R ⧸ I) A₀]
        [FinitePresentation (R ⧸ I) A₀]
        (φ₀ : A₀ →ₐ[R ⧸ I] L ⧸ I.map (algebraMap R L)),
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra (R ⧸ I) B₀),
        Smooth (R ⧸ I) B₀ ∧
          ∃ (α₀ : A₀ →ₐ[R ⧸ I] B₀)
            (β₀ : B₀ →ₐ[R ⧸ I] L ⧸ I.map (algebraMap R L)),
            β₀.comp α₀ = φ₀)
    {A : Type u} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] L) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : A →ₐ[R] D) (β : D →ₐ[R] L), β.comp α = φ := by
  let IL := I.map (algebraMap R L)
  have hIL : IL ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn⟩ := hI
    have hpow : IL ^ n = ⊥ := by
      change I.map (algebraMap R L) ^ n = ⊥
      rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    rw [htop, Ideal.top_pow] at hpow
    exact top_ne_bot hpow
  have : Nontrivial (L ⧸ IL) := Ideal.Quotient.nontrivial_iff.mpr hIL
  have : IsLocalRing (L ⧸ IL) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IL) Ideal.Quotient.mk_surjective
  apply exists_smooth_factorization_of_nilpotent_modulo_factorizations I ?_ hI φ
  intro A₀ _ _ _ φ₀
  obtain ⟨B₀, _, _, hB₀, α₀, β₀, hfac₀⟩ := hmod A₀ φ₀
  have : Smooth (R ⧸ I) B₀ := hB₀
  obtain ⟨f, hstd, ψ, hψ⟩ :=
    Smooth.exists_standardSmooth_localization_factorization β₀
  refine ⟨Localization.Away f, inferInstance, inferInstance, hstd,
    (IsScalarTower.toAlgHom (R ⧸ I) B₀ (Localization.Away f)).comp α₀, ψ, ?_⟩
  rw [← AlgHom.comp_assoc, hψ, hfac₀]

end Algebra
