/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.NilpotentFlatRelationLift
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Lifting a flat relation across a square-zero quotient

The equational criterion for flatness constructs a finitely presented
relation algebra retaining the original map. After this algebra has
been factored through a square-zero quotient, formal smoothness lifts
the original smooth source. The lifted map kills the original weighted
relation because all coefficients lie in the square-zero base ideal.
Its composite to the original target is exact.

These are the concrete relation-algebra and cancellation steps in
Stacks Project, Lemma 16.5.2:
https://stacks.math.columbia.edu/tag/07CL
-/

@[expose] public section

noncomputable section

universe u v w

namespace Algebra

/-- A vanishing finite relation in a flat target is trivialized inside
a finitely presented algebra through which the original map factors. -/
theorem exists_finitePresentation_trivializing_relation
    {R : Type u} {B : Type v} {L : Type w}
    [CommRing R] [CommRing B] [CommRing L] [Algebra R B] [Algebra R L]
    [FinitePresentation R B] [Module.Flat R L]
    {ι : Type*} [Fintype ι] (φ : B →ₐ[R] L) (ε : ι → R) (b : ι → B)
    (h : φ (∑ i, ε i • b i) = 0) :
    ∃ (m : ℕ) (a : ι → Fin m → R)
      (C : Type v) (_ : CommRing C) (_ : Algebra R C),
      FinitePresentation R C ∧
        ∃ (γ : B →ₐ[R] C) (δ : C →ₐ[R] L) (ξ : Fin m → C),
          δ.comp γ = φ ∧ (∀ i, γ (b i) = ∑ j, a i j • ξ j) ∧
            ∀ j, ∑ i, ε i * a i j = 0 := by
  classical
  have h' : ∑ i, ε i • φ (b i) = 0 := by
    simpa only [map_sum, map_smul] using h
  obtain ⟨m, a, y, hb, ha⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  let D := MvPolynomial (Fin m) B
  let r : ι → D := fun i => MvPolynomial.C (b i) - ∑ j, a i j • MvPolynomial.X j
  let J : Ideal D := Ideal.span (Set.range r)
  have hJfg : J.FG := by
    exact ⟨(Set.finite_range r).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have : FinitePresentation R D := FinitePresentation.trans R B D
  have : FinitePresentation R (D ⧸ J) := FinitePresentation.quotient hJfg
  let f : D →ₐ[R] L := MvPolynomial.aevalTower φ y
  have hfC (b' : B) : f (MvPolynomial.C b') = φ b' :=
    MvPolynomial.aevalTower_C φ y b'
  have hfX (j : Fin m) : f (MvPolynomial.X j) = y j :=
    MvPolynomial.aevalTower_X φ y j
  have hJf : J ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (MvPolynomial.C (b i) - ∑ j, a i j • MvPolynomial.X j) = 0
    rw [map_sub, map_sum, hfC]
    simp only [map_smul, hfX]
    rw [← hb i, sub_self]
  let q : D →ₐ[R] D ⧸ J := Ideal.Quotient.mkₐ R J
  let γ : B →ₐ[R] D ⧸ J := q.comp (IsScalarTower.toAlgHom R B D)
  let δ : D ⧸ J →ₐ[R] L := Ideal.Quotient.liftₐ J f hJf
  let ξ : Fin m → D ⧸ J := fun j => q (MvPolynomial.X j)
  refine ⟨m, a, D ⧸ J, inferInstance, inferInstance, inferInstance,
    γ, δ, ξ, ?_, ?_, ha⟩
  · apply AlgHom.ext
    intro b'
    exact MvPolynomial.aevalTower_C φ y b'
  · intro i
    have hri : q (r i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    change q (MvPolynomial.C (b i) - ∑ j, a i j • MvPolynomial.X j) = 0 at hri
    rw [map_sub, map_sum] at hri
    simp only [map_smul] at hri
    exact sub_eq_zero.mp hri

/-- A formal smooth lift kills a weighted relation whose coefficient
relations already vanish, when the coefficients lie in a square-zero
base ideal. The map to the original target still has its exact
composite through the supplied quotient factorization. -/
theorem exists_lift_killing_relation_of_squareZero
    {R B C D L : Type*}
    [CommRing R] [CommRing B] [CommRing C] [CommRing D] [CommRing L]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R L]
    [FormallySmooth R B]
    (I : Ideal R) (hI : I ^ 2 = ⊥) (J : Ideal D)
    (hJI : J ≤ I.map (algebraMap R D))
    (γ : B →ₐ[R] C) (η : C →ₐ[R] D ⧸ J) (β : D ⧸ J →ₐ[R] L)
    {ι : Type*} [Fintype ι] {m : ℕ}
    (ε : ι → R) (hε : ∀ i, ε i ∈ I) (b : ι → B)
    (a : ι → Fin m → R) (ξ : Fin m → C)
    (hb : ∀ i, γ (b i) = ∑ j, a i j • ξ j)
    (ha : ∀ j, ∑ i, ε i * a i j = 0) :
    ∃ α : B →ₐ[R] D,
      α (∑ i, ε i • b i) = 0 ∧
        (β.comp (Ideal.Quotient.mkₐ R J)).comp α = β.comp (η.comp γ) := by
  obtain ⟨α, hmem, hcomp⟩ :=
    exists_lift_relation_mem_mul_of_nilpotent
      I ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩ I J hJI γ η β ε hε b a ξ hb ha
  rw [← pow_two, hI, Ideal.map_bot] at hmem
  exact ⟨α, Ideal.mem_bot.mp hmem, hcomp⟩

end Algebra
