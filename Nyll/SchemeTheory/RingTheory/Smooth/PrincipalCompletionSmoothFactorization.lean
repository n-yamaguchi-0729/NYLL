/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PoweredStrictStandardSmoothFactorization
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionLocalRing
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Actual approximation and smooth factorization in a principal completion

Projection to the original ideal-power quotient produces the approximate
coordinates. The same projection proves divisibility of every original
relation. Powering and cubic correction therefore construct a smooth
factorization of the original map to the principal completion, without
an approximate section or a smooth algebra being supplied.
-/

@[expose] public section

noncomputable section

universe u w t z

open MvPolynomial IsLocalRing
open scoped Matrix

namespace AdicCompletion

/-- Completion along a finitely generated ideal contained in the maximal
ideal of a local ring is local. The proof uses actual coefficient
approximation and the units congruent to one in the completion. -/
theorem isLocalRing_of_le_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.FG) (hle : I ≤ maximalIdeal R) :
    IsLocalRing (AdicCompletion I R) := by
  have hne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hle
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : Nontrivial (AdicCompletion I R) := (evalOneₐ I).toRingHom.domain_nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  obtain ⟨a, y, hy, hxy⟩ := exists_eq_algebraMap_add I hI 1 x
  rw [pow_one] at hy
  obtain ha | ha := IsLocalRing.isUnit_or_isUnit_one_sub_self a
  · apply Or.inl
    rw [hxy]
    exact isUnit_add_of_mem_map I hI (ha.map (algebraMap R _)) hy
  · apply Or.inr
    have heq : 1 - x = algebraMap R (AdicCompletion I R) (1 - a) + -y := by
      rw [hxy, map_sub, map_one]
      ring
    rw [heq]
    exact isUnit_add_of_mem_map I hI (ha.map (algebraMap R _))
      ((I.map (algebraMap R (AdicCompletion I R))).neg_mem hy)

/-- The actual coefficient map to completion along a proper ideal in a
local ring reflects units. -/
theorem isLocalHom_algebraMap_of_le_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hle : I ≤ maximalIdeal R) :
    IsLocalHom (algebraMap R (AdicCompletion I R)) := by
  have hne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hle
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  constructor
  intro a ha
  apply isUnit_of_map_unit (Ideal.Quotient.mk I) a
  have h := ha.map (evalOneₐ I).toRingHom
  exact h

/-- Every actual polynomial-quotient map to the principal completion has
an approximate section of every order. The same section approximates its
original coordinates and annihilates all its original relations modulo
the specified parameter power. -/
theorem exists_principal_approximate_section
    {R : Type u} {m : Type w} {n : Type t} {k : Type z} [CommRing R]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (φ : (MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
      AdicCompletion (Ideal.span {π}) R)
    (N : ℕ) :
    ∃ a : n → R,
      (∀ j, π ^ N ∣ aeval a (f j)) ∧
      (∀ j, π ^ N ∣ aeval a (h j)) ∧
      ∃ zeta : n → AdicCompletion (Ideal.span {π}) R,
        ∀ i, φ (Ideal.Quotient.mk
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i)) -
          algebraMap R (AdicCompletion (Ideal.span {π}) R) (a i) =
            algebraMap R (AdicCompletion (Ideal.span {π}) R) π ^ N * zeta i := by
  classical
  let I : Ideal R := Ideal.span {π}
  let J : Ideal (MvPolynomial n R) :=
    Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)
  let q : MvPolynomial n R →ₐ[R] (MvPolynomial n R ⧸ J) := Ideal.Quotient.mkₐ R J
  let e : AdicCompletion I R →ₐ[R] R ⧸ I ^ N := evalₐ I N
  choose a ha using fun i : n => Ideal.Quotient.mk_surjective (e (φ (q (X i))))
  have hmap : (e.comp φ).comp q = (Ideal.Quotient.mkₐ R (I ^ N)).comp (aeval a) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk] using (ha i).symm
  have hrelations (p : MvPolynomial n R) (hp : p ∈ J) : π ^ N ∣ aeval a p := by
    have heval : Ideal.Quotient.mk (I ^ N) (aeval a p) = 0 := by
      change ((Ideal.Quotient.mkₐ R (I ^ N)).comp (aeval a)) p = 0
      rw [← hmap]
      change e (φ (q p)) = 0
      rw [show q p = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hp, _root_.map_zero, _root_.map_zero]
    have hp' := Ideal.Quotient.eq_zero_iff_mem.mp heval
    rw [show I = Ideal.span {π} from rfl, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hp'
    exact hp'
  have hcoordinates (i : n) : ∃ zeta : AdicCompletion I R,
      φ (q (X i)) - algebraMap R (AdicCompletion I R) (a i) =
        algebraMap R (AdicCompletion I R) π ^ N * zeta := by
    have hx : φ (q (X i)) - algebraMap R (AdicCompletion I R) (a i) ∈
        RingHom.ker (evalₐ I N) := by
      rw [RingHom.mem_ker, map_sub, evalₐ_algebraMap]
      exact sub_eq_zero.mpr (ha i).symm
    rw [ker_evalₐ_eq_map_pow I (Submodule.fg_span_singleton π)] at hx
    change φ (q (X i)) - algebraMap R (AdicCompletion I R) (a i) ∈
      (Ideal.span {π} ^ N).map (algebraMap R (AdicCompletion I R)) at hx
    rw [Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, map_pow, Ideal.mem_span_singleton] at hx
    exact hx
  choose zeta hzeta using hcoordinates
  refine ⟨a, fun j => hrelations (f j) ?_, fun j => hrelations (h j) ?_, zeta, hzeta⟩
  · exact (show Ideal.span (Set.range f) ≤ J from le_sup_left)
      (Ideal.subset_span (Set.mem_range_self j))
  · exact (show Ideal.span (Set.range h) ≤ J from le_sup_right)
      (Ideal.subset_span (Set.mem_range_self j))

end AdicCompletion

namespace Algebra

/-- Original strictly-standard data for a base parameter in the maximal
ideal give an actual smooth factorization of every original map to its
principal completion. The approximate section and required parameter
power are both produced in the proof. -/
theorem exists_smooth_factorization_principalCompletion_of_strictStandard_data
    {R : Type u} {m : Type w} {n : Type t} {k : Type z}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : π ∈ maximalIdeal R)
    (φ : (MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
      AdicCompletion (Ideal.span {π}) R) :
    ∃ (D : Type (max u w t)) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧
        ∃ (α : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] D)
          (β : D →ₐ[R] AdicCompletion (Ideal.span {π}) R), β.comp α = φ := by
  let I : Ideal R := Ideal.span {π}
  have hle : I ≤ maximalIdeal R := (maximalIdeal R).span_singleton_le_iff_mem.mpr hπ
  have : IsLocalRing (AdicCompletion I R) :=
    AdicCompletion.isLocalRing_of_le_maximalIdeal I (Submodule.fg_span_singleton π) hle
  have : IsNoetherianRing (AdicCompletion I R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing I
  have : IsLocalHom (algebraMap R (AdicCompletion I R)) :=
    AdicCompletion.isLocalHom_algebraMap_of_le_maximalIdeal I hle
  have hπ' : algebraMap R (AdicCompletion I R) π ∈ maximalIdeal (AdicCompletion I R) :=
    map_nonunit (algebraMap R (AdicCompletion I R)) π hπ
  obtain ⟨N, _, hN⟩ := exists_power_smooth_factorization_of_strictStandard_data
    (L := AdicCompletion I R) π f h hminor hrelations hπ'
  obtain ⟨a, hf, hh, zeta, hzeta⟩ :=
    AdicCompletion.exists_principal_approximate_section π f h φ (N * 4)
  have hf' (j : m) : (π ^ N) ^ 4 ∣ aeval a (f j) := by
    simpa only [pow_mul] using hf j
  have hh' (j : k) : (π ^ N) ^ 4 ∣ aeval a (h j) := by
    simpa only [pow_mul] using hh j
  have hzeta' (i : n) : φ (Ideal.Quotient.mk
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i)) -
      algebraMap R (AdicCompletion I R) (a i) =
        algebraMap R (AdicCompletion I R) (π ^ N) ^ 4 * zeta i := by
    simpa only [map_pow, pow_mul] using hzeta i
  exact hN a hf' hh' φ zeta hzeta'

end Algebra
