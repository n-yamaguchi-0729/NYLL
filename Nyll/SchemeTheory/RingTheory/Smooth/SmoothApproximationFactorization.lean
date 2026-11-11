/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingSmoothSource
public import Nyll.SchemeTheory.RingTheory.Smooth.GeneralApproximationFactorization

/-!
# Smooth factorization from a smooth principal approximation

An actual smooth factorization modulo a sufficiently high power first gives
a smooth lifting algebra by the principal lifting construction. Its original
reduction triangle supplies a compatible quotient section for uniform
relative correction. The resulting smooth algebra factors the original map
exactly. The power is chosen before the smooth quotient factorization.

This is the smooth-source case of Stacks, `lemma-desingularize-lifting-apply`.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace Algebra

/-- Lift an actual square-modulus factorization through a smooth quotient
algebra to a smooth algebra with a compatible first-order section. -/
theorem exists_smooth_lift_of_quotient_factorization
    {R : Type u} {L : Type v} {A : Type w} {Cbar : Type z}
    [CommRing R] [CommRing L] [CommRing A] [CommRing Cbar]
    [Algebra R L] [Algebra R A] [Algebra R Cbar] [IsNoetherianRing R]
    (q : R) [Algebra (R ⧸ Ideal.span {q ^ 2}) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span {q ^ 2}) Cbar]
    [Smooth (R ⧸ Ideal.span {q ^ 2}) Cbar]
    (hstableR : ∀ x : R, q ^ 2 * x = 0 → q * x = 0)
    (hstableL : ∀ x : L, (algebraMap R L q) ^ 2 * x = 0 →
      algebraMap R L q * x = 0)
    (σ : (A ⧸ Ideal.span {(algebraMap R A q) ^ 2}) →ₐ[R] Cbar)
    (α : Cbar →ₐ[R] L ⧸ Ideal.span {(algebraMap R L q) ^ 2})
    (φ : A →ₐ[R] L)
    (hfactor : α.comp (σ.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {(algebraMap R A q) ^ 2}))) =
      (Ideal.Quotient.mkₐ R (Ideal.span {(algebraMap R L q) ^ 2})).comp φ) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D), Smooth R D ∧
      ∃ (β : D →ₐ[R] L) (ρ : A →ₐ[R] D ⧸ Ideal.span {algebraMap R D q})
        (δ : (D ⧸ Ideal.span {algebraMap R D q}) →+*
          L ⧸ Ideal.span {algebraMap R L q}),
        δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D q})) =
          (Ideal.Quotient.mk (Ideal.span {algebraMap R L q})).comp β.toRingHom ∧
        δ.comp ρ.toRingHom =
          (Ideal.Quotient.mk (Ideal.span {algebraMap R L q})).comp φ.toRingHom := by
  obtain ⟨D, _, _, hfp, haway, β, ρ, _γ, δ, _ε, hδ, _hε, _htriangle, hρ, hclosed⟩ :=
    exists_principal_lift_of_quotient_factorization q hstableR hstableL σ α φ hfactor
  have : FinitePresentation R D := hfp
  have : Smooth R (Localization.Away (algebraMap R D q)) := haway
  have hsm : Smooth R D := smooth_of_away_and_principal_quotient
    (algebraMap R D q) (fun p => hclosed p (by
      rw [smoothLocus_eq_univ]
      exact Set.mem_univ _))
  exact ⟨D, inferInstance, inferInstance, hsm, β, ρ, δ, hδ, hρ⟩

open MvPolynomial

/-- Choose a positive power before the quotient factorization. Any actual
smooth factorization modulo `(π^(4*N))² = π^(8*N)` then constructs an exact
smooth factorization of the original algebra map. The only approximation
input is the displayed quotient factorization. -/
theorem exists_uniform_power_smooth_factorization_of_smooth_quotient_factorization
    {R L m n k : Type u}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [IsNoetherianRing L]
    [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L) :
    ∃ N : ℕ, 0 < N ∧
      let q := π ^ (4 * N)
      let A := MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))
      ∀ (Cbar : Type u) [CommRing Cbar]
        [Algebra (R ⧸ Ideal.span {q ^ 2}) Cbar]
        [Smooth (R ⧸ Ideal.span {q ^ 2}) Cbar],
        let _ : Algebra R Cbar :=
          ((algebraMap (R ⧸ Ideal.span {q ^ 2}) Cbar).comp
            (algebraMap R (R ⧸ Ideal.span {q ^ 2}))).toAlgebra
        ∀ (σ : (A ⧸ Ideal.span {(algebraMap R A q) ^ 2}) →ₐ[R] Cbar)
          (α : Cbar →ₐ[R] L ⧸ Ideal.span {(algebraMap R L q) ^ 2})
          (φ : A →ₐ[R] L),
          α.comp (σ.comp (Ideal.Quotient.mkₐ R
              (Ideal.span {(algebraMap R A q) ^ 2}))) =
            (Ideal.Quotient.mkₐ R (Ideal.span {(algebraMap R L q) ^ 2})).comp φ →
          ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E), Smooth R E ∧
            ∃ (a : A →ₐ[R] E) (b : E →ₐ[R] L), b.comp a = φ := by
  obtain ⟨N, hN, hproduce⟩ :=
    exists_uniform_power_desingularization_of_quotient_factorization
      (L := L) π f h hminor hrelations hπ
  refine ⟨N, hN, ?_⟩
  intro q A Cbar _ _ _ hRCbar σ α φ hfactor
  obtain ⟨E, _, _, hfp, haway, a, c, hca,
      _Γ, _δ, _ε, _hδ, _hε, _htriangle, hclosed⟩ :=
    hproduce Cbar σ α φ hfactor
  have : FinitePresentation R E := hfp
  have : Smooth R (Localization.Away (algebraMap R E q)) := by
    apply (basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := E)).mp
    intro p hp
    apply (basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := E)).mpr haway
    intro hmem
    apply hp
    rw [show q = π ^ (4 * N) from rfl, map_pow]
    exact p.asIdeal.pow_mem_of_mem hmem (4 * N) (Nat.mul_pos (by decide) hN)
  have hsm : Smooth R E := smooth_of_away_and_principal_quotient
    (algebraMap R E q) (fun p => hclosed p (by
      rw [smoothLocus_eq_univ]
      exact Set.mem_univ _))
  exact ⟨E, inferInstance, inferInstance, hsm, a, c, hca⟩

end Algebra
