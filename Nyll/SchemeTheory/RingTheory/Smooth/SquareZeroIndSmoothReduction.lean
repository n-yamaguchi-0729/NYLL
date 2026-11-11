/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SquareZeroSmoothFactorization
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lifting smooth factorizations across nilpotent base ideals

Finite induction removes all generators of the relation ideal from a
smooth quotient factorization. The quotient map then factors through
the resulting smooth algebra, with its original composite unchanged.

The modulo-ideal factorization hypothesis is the induction hypothesis
of the nilpotent reduction in Stacks Project, Lemmas 16.5.2 and 16.5.3:
https://stacks.math.columbia.edu/tag/07CL
https://stacks.math.columbia.edu/tag/07CM
-/

@[expose] public section

noncomputable section

universe u v

namespace Algebra

variable {R : Type u} {L : Type v}
  [CommRing R] [CommRing L] [Algebra R L] [Module.Flat R L]
  (I : Ideal R)
  (hmod : ∀ (A₀ : Type u) [CommRing A₀] [Algebra (R ⧸ I) A₀]
      [FinitePresentation (R ⧸ I) A₀]
      (φ₀ : A₀ →ₐ[R ⧸ I] L ⧸ I.map (algebraMap R L)),
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra (R ⧸ I) B₀),
      IsStandardSmooth (R ⧸ I) B₀ ∧
        ∃ (α₀ : A₀ →ₐ[R ⧸ I] B₀)
          (β₀ : B₀ →ₐ[R ⧸ I] L ⧸ I.map (algebraMap R L)),
          β₀.comp α₀ = φ₀)

section Nilpotent

variable (hI : IsNilpotent I)

include hmod hI

private theorem exists_smooth_factorization_killing_finset
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) (s : Finset B)
    (hmem : ∀ x ∈ s, x ∈ I.map (algebraMap R B))
    (hker : ∀ x ∈ s, φ x = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ ∀ x ∈ s, α x = 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨B, inferInstance, inferInstance, inferInstance,
      AlgHom.id R B, φ, AlgHom.comp_id φ, ?_⟩
    intro x hx
    exact False.elim (Finset.notMem_empty x hx)
  | @insert x s hxs ih =>
    obtain ⟨D, _, _, hD, α, β, hfac, hkill⟩ :=
      ih (fun b hb => hmem b (Finset.mem_insert_of_mem hb))
        (fun b hb => hker b (Finset.mem_insert_of_mem hb))
    have : Smooth R D := hD
    have hle : I.map (algebraMap R B) ≤
        (I.map (algebraMap R D)).comap α.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change α (algebraMap R B r) ∈ I.map (algebraMap R D)
      rw [α.commutes]
      exact Ideal.mem_map_of_mem (algebraMap R D) hr
    have hx : α x ∈ I.map (algebraMap R D) :=
      hle (hmem x (Finset.mem_insert_self x s))
    have hβx : β (α x) = 0 := by
      have hf := AlgHom.congr_fun hfac x
      exact hf.trans (hker x (Finset.mem_insert_self x s))
    obtain ⟨E, _, _, hE, γ, δ, hγδ, hγx⟩ :=
      exists_smooth_factorization_killing_element_of_nilpotent
        I hmod hI β (α x) hx hβx
    refine ⟨E, inferInstance, inferInstance, hE, γ.comp α, δ, ?_, ?_⟩
    · rw [← AlgHom.comp_assoc, hγδ, hfac]
    · intro b hb
      obtain rfl | hb := Finset.mem_insert.mp hb
      · exact hγx
      · change γ (α b) = 0
        rw [hkill b hb, map_zero]

/-- All generators of an ideal contained in `I B ∩ ker φ` can be removed
by one actual smooth factorization. -/
theorem exists_smooth_factorization_killing_fgIdeal_of_nilpotent
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) (J : Ideal B) (hJfg : J.FG)
    (hJI : J ≤ I.map (algebraMap R B))
    (hJφ : J ≤ RingHom.ker φ.toRingHom) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ J ≤ RingHom.ker α.toRingHom := by
  obtain ⟨s, hs⟩ := hJfg
  have hsJ : Ideal.span (s : Set B) = J := hs
  have hmem (x : B) (hx : x ∈ s) : x ∈ J := by
    rw [← hsJ]
    exact Ideal.subset_span hx
  obtain ⟨D, _, _, hD, α, β, hfac, hkill⟩ :=
    exists_smooth_factorization_killing_finset I hmod hI φ s
      (fun x hx => hJI (hmem x hx)) (fun x hx => hJφ (hmem x hx))
  refine ⟨D, inferInstance, inferInstance, hD, α, β, hfac, ?_⟩
  rw [← hsJ]
  exact Ideal.span_le.mpr fun x hx => hkill x hx

/-- The nilpotent lifting step: the original modulo-ideal smooth
factorization hypothesis produces an actual smooth factorization over
the original base. -/
theorem exists_smooth_factorization_of_nilpotent_modulo_factorizations
    {A : Type u} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] L) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : A →ₐ[R] D) (β : D →ₐ[R] L), β.comp α = φ := by
  obtain ⟨B, _, _, hB, J, hJfg, hJI, α, β, hfac⟩ :=
    exists_smooth_quotient_factorization_of_modulo_factorizations I hmod hI φ
  have : Smooth R B := hB
  let q : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  let ψ : B →ₐ[R] L := β.comp q
  have hJψ : J ≤ RingHom.ker ψ.toRingHom := by
    intro b hb
    change β (q b) = 0
    rw [show q b = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
  obtain ⟨D, _, _, hD, γ, δ, hγδ, hJγ⟩ :=
    exists_smooth_factorization_killing_fgIdeal_of_nilpotent I hmod hI ψ J hJfg hJI hJψ
  let γq : B ⧸ J →ₐ[R] D := Ideal.Quotient.liftₐ J γ hJγ
  have hγqδ : δ.comp γq = β := by
    apply AlgHom.ext
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact AlgHom.congr_fun hγδ b
  refine ⟨D, inferInstance, inferInstance, hD, γq.comp α, δ, ?_⟩
  rw [← AlgHom.comp_assoc, hγqδ, hfac]

end Nilpotent

include hmod

/-- The square-zero specialization of finite ideal removal. -/
theorem exists_smooth_factorization_killing_fgIdeal_of_squareZero
    (hI : I ^ 2 = ⊥)
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) (J : Ideal B) (hJfg : J.FG)
    (hJI : J ≤ I.map (algebraMap R B))
    (hJφ : J ≤ RingHom.ker φ.toRingHom) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ J ≤ RingHom.ker α.toRingHom :=
  exists_smooth_factorization_killing_fgIdeal_of_nilpotent
    I hmod ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩ φ J hJfg hJI hJφ

/-- The square-zero specialization of nilpotent smooth factorization. -/
theorem exists_smooth_factorization_of_squareZero_modulo_factorizations
    (hI : I ^ 2 = ⊥)
    {A : Type u} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] L) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : A →ₐ[R] D) (β : D →ₐ[R] L), β.comp α = φ :=
  exists_smooth_factorization_of_nilpotent_modulo_factorizations
    I hmod ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩ φ

end Algebra
