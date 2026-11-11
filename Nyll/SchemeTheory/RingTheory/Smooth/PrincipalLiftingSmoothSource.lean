/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingExistence
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# A smooth lifting of a smooth principal-square approximation

The principal lifting construction supplies smoothness away from the
parameter and above the original source's smooth locus. For a smooth
source these two loci cover the entire constructed algebra. Its target
map and both reduction triangles are retained.

This is the smooth-source case of the lifting step used in the Stacks
Project proof following https://stacks.math.columbia.edu/tag/07CP.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Algebra

/-- Smoothness away from a parameter and at every prime of its closed
complement covers the entire finitely presented algebra. The latter primes
are taken in the actual principal quotient. -/
theorem smooth_of_away_and_principal_quotient
    {R D : Type*} [CommRing R] [CommRing D] [Algebra R D]
    [FinitePresentation R D] (d : D)
    [Smooth R (Localization.Away d)]
    (hclosed : ∀ p : PrimeSpectrum (D ⧸ Ideal.span {d}),
      IsSmoothAt R (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {d})) p).asIdeal) :
    Smooth R D := by
  have hall : smoothLocus R D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    by_cases hd : d ∈ q.asIdeal
    · have hI : Ideal.span {d} ≤ q.asIdeal :=
        (Ideal.span_singleton_le_iff_mem _).mpr hd
      have hrange : q ∈ Set.range
          (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {d}))) := by
        rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
        change RingHom.ker (Ideal.Quotient.mk (Ideal.span {d})) ≤ q.asIdeal
        intro x hx
        exact hI (Ideal.Quotient.eq_zero_iff_mem.mp hx)
      obtain ⟨p, rfl⟩ := hrange
      exact hclosed p
    · exact (basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := D)).mpr
        inferInstance hd
  exact ⟨smoothLocus_eq_univ_iff.mp hall, inferInstance⟩

/-- An actual smooth algebra modulo `π²`, with its approximate target map,
produces a smooth algebra over the original base and an exact target map.
The source map modulo `π` and the commuting reduction triangle are part of
the constructed output; no lifting algebra is supplied as a premise. -/
theorem exists_smooth_principal_lifting
    {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    [IsNoetherianRing R]
    (π : R) (hstableR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (hstableL : ∀ x : L, (algebraMap R L π) ^ 2 * x = 0 →
      algebraMap R L π * x = 0)
    {B : Type w} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    [Smooth (R ⧸ Ideal.span {π ^ 2}) B]
    (α : B →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2})
    (hα : ∀ r : R,
      α (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2}) (algebraMap R L r)) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D), Smooth R D ∧
      ∃ (β : D →ₐ[R] L) (γ : B →+* D ⧸ Ideal.span {algebraMap R D π}),
        (∀ r : R, γ (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (algebraMap R D r)) ∧
        ∃ (δ : (D ⧸ Ideal.span {algebraMap R D π}) →+*
              L ⧸ Ideal.span {algebraMap R L π})
            (ε : (L ⧸ Ideal.span {(algebraMap R L π) ^ 2}) →+*
              L ⧸ Ideal.span {algebraMap R L π}),
          δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) =
            (Ideal.Quotient.mk (Ideal.span {algebraMap R L π})).comp β.toRingHom ∧
          ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})) =
            Ideal.Quotient.mk (Ideal.span {algebraMap R L π}) ∧
          δ.comp γ = ε.comp α := by
  obtain ⟨D, _, _, hfp, haway, β, γ, hγ, htriangle, hclosed⟩ :=
    exists_principal_lifting_with_source_smoothLocus π hstableR hstableL α hα
  have : FinitePresentation R D := hfp
  have : Smooth R (Localization.Away (algebraMap R D π)) := haway
  have hsm : Smooth R D := smooth_of_away_and_principal_quotient
    (algebraMap R D π) (fun p => hclosed p (by
      rw [smoothLocus_eq_univ]
      exact Set.mem_univ _))
  exact ⟨D, inferInstance, inferInstance, hsm, β, γ, hγ, htriangle⟩

end Algebra
