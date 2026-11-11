/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PoweredStrictStandardSmoothFactorization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coordinates supplied by an actual quotient section

A section into a principal quotient supplies representatives of all original
coordinates. Compatibility with a target map gives the exact coordinate
errors, while every original relation evaluates into the principal ideal.
No coordinate divisibility or approximate solution is assumed separately.
-/

@[expose] public section

noncomputable section

universe u v w t z

namespace MvPolynomial

/-- Representatives of a compatible quotient section solve every original
relation modulo the specified parameter and recover the target coordinates
modulo its image. -/
theorem exists_coordinates_of_quotient_section
    {R : Type u} {L : Type v} {n : Type w}
    [CommRing R] [CommRing L] [Algebra R L]
    (I : Ideal (MvPolynomial n R)) (q : R)
    (ρ : (MvPolynomial n R ⧸ I) →ₐ[R] R ⧸ Ideal.span {q})
    (φ : (MvPolynomial n R ⧸ I) →ₐ[R] L)
    (hcompat : (Ideal.Quotient.mkₐ R ((Ideal.span {q}).map (algebraMap R L))).comp φ =
      (Ideal.quotientMapₐ ((Ideal.span {q}).map (algebraMap R L))
        (Algebra.ofId R L) Ideal.le_comap_map).comp ρ) :
    ∃ a : n → R, (∀ p ∈ I, q ∣ aeval a p) ∧
      ∀ i, algebraMap R L q ∣
        φ (Ideal.Quotient.mk I (X i)) - algebraMap R L (a i) := by
  classical
  let K : Ideal R := Ideal.span {q}
  let J : Ideal L := K.map (algebraMap R L)
  choose a ha using fun i : n => Ideal.Quotient.mk_surjective
    (ρ (Ideal.Quotient.mk I (X i)))
  have heval : (Ideal.Quotient.mkₐ R K).comp (aeval a) =
      ρ.comp (Ideal.Quotient.mkₐ R I) := by
    apply algHom_ext
    intro i
    change Ideal.Quotient.mk K (aeval a (X i)) = ρ (Ideal.Quotient.mk I (X i))
    rw [aeval_X]
    exact ha i
  refine ⟨a, ?_, ?_⟩
  · intro p hp
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := AlgHom.congr_fun heval p
    change Ideal.Quotient.mk K (aeval a p) = ρ (Ideal.Quotient.mk I p) at he
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero] at he
    exact he
  · intro i
    have hc := AlgHom.congr_fun hcompat (Ideal.Quotient.mk I (X i))
    change Ideal.Quotient.mk J (φ (Ideal.Quotient.mk I (X i))) =
      Ideal.quotientMap J (algebraMap R L) Ideal.le_comap_map
        (ρ (Ideal.Quotient.mk I (X i))) at hc
    rw [← ha i, Ideal.quotientMap_mk] at hc
    have hd : φ (Ideal.Quotient.mk I (X i)) - algebraMap R L (a i) ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hc, sub_self]
    have hJ : J = Ideal.span {algebraMap R L q} := by
      change Ideal.map (algebraMap R L) (Ideal.span {q}) = _
      rw [Ideal.map_span, Set.image_singleton]
    rw [hJ] at hd
    exact Ideal.mem_span_singleton.mp hd

end MvPolynomial

open MvPolynomial
open scoped Matrix

namespace Algebra

/-- A compatible quotient section constructs the actual residual quotient.
No base annihilator stability or target-unit controller is assumed. -/
theorem exists_residual_quotient_factorization_of_quotient_section
    {R : Type u} {L : Type v} {m : Type w} {n : Type t} {k : Type z}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstableL : ∀ x : L,
      algebraMap R L π ^ 2 * x = 0 → algebraMap R L π * x = 0)
    (ρ : (MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
      R ⧸ Ideal.span {π ^ 4})
    (φ : (MvPolynomial n R ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L)
    (hcompat :
      (Ideal.Quotient.mkₐ R ((Ideal.span {π ^ 4}).map (algebraMap R L))).comp φ =
        (Ideal.quotientMapₐ ((Ideal.span {π ^ 4}).map (algebraMap R L))
          (Algebra.ofId R L) Ideal.le_comap_map).comp ρ) :
    ∃ (B : Type (max u w t)) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ J : Ideal B,
        J.FG ∧ J ≤ Ideal.span {algebraMap R B π ^ 2} ∧
        Ideal.span {algebraMap R B π} * J ≤ J ^ 2 ∧
        ∃ (α : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] B ⧸ J)
          (β : B ⧸ J →ₐ[R] L), β.comp α = φ := by
  classical
  let I : Ideal (MvPolynomial n R) :=
    Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)
  obtain ⟨a, ha, hcoordinates⟩ :=
    MvPolynomial.exists_coordinates_of_quotient_section I (π ^ 4) ρ φ hcompat
  let J : Ideal (MvPolynomial n R) := Ideal.span (Set.range fun c : m → n =>
    ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det)
  let K : Ideal R := Ideal.span {π ^ 4}
  let M : Matrix m n R := Matrix.of fun j i => aeval a (pderiv i (f j))
  let J₀ : Ideal R := Ideal.span (Set.range fun c : m → n =>
    (M.submatrix _root_.id c).det)
  let e : MvPolynomial n R →+* R := (aeval a).toRingHom
  have heI : Ideal.map e I ≤ K := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    exact Ideal.mem_span_singleton.mpr (ha p hp)
  have heJ : Ideal.map e J ≤ J₀ := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change e (((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det) ∈ J₀
    rw [RingHom.map_det]
    exact Ideal.subset_span (Set.mem_range_self c)
  have heAll : Ideal.map e (I ⊔ J) ≤ K ⊔ J₀ := by
    rw [Ideal.map_sup]
    exact sup_le_sup heI heJ
  have hminor' : π ∈ J₀ ⊔ K := by
    have hp := heAll (Ideal.mem_map_of_mem e hminor)
    change aeval a (C π) ∈ K ⊔ J₀ at hp
    rw [aeval_C, Algebra.algebraMap_self_apply] at hp
    simpa only [sup_comm] using hp
  have hf (j : m) : π ^ 4 ∣ aeval a (f j) :=
    ha (f j) ((show Ideal.span (Set.range f) ≤ I from le_sup_left)
      (Ideal.subset_span (Set.mem_range_self j)))
  have hh (j : k) : π ^ 4 ∣ aeval a (h j) :=
    ha (h j) ((show Ideal.span (Set.range h) ≤ I from le_sup_right)
      (Ideal.subset_span (Set.mem_range_self j)))
  choose zeta hzeta using hcoordinates
  have hzeta' (i : n) : φ (Ideal.Quotient.mk I (X i)) - algebraMap R L (a i) =
      algebraMap R L π ^ 4 * zeta i := by
    simpa only [map_pow] using hzeta i
  exact exists_residual_quotient_factorization_at_approximate_section
    π f h a hminor' hf hh hrelations hπ hstableL φ zeta hzeta'

/-- A genuine quotient section for the fixed fourth-order parameter
constructs a smooth factorization of the original map. Its original
polynomial strictly-standard memberships supply the evaluated Jacobian
condition, and the quotient compatibility supplies every coordinate error.
The parameter is fixed before this construction. -/
theorem exists_smooth_factorization_of_quotient_section
    {R : Type u} {L : Type v} {m : Type w} {n : Type t} {k : Type z}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstableR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (hstableL : ∀ x : L,
      algebraMap R L π ^ 2 * x = 0 → algebraMap R L π * x = 0)
    (ρ : (MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
      R ⧸ Ideal.span {π ^ 4})
    (φ : (MvPolynomial n R ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L)
    (hcompat :
      (Ideal.Quotient.mkₐ R ((Ideal.span {π ^ 4}).map (algebraMap R L))).comp φ =
        (Ideal.quotientMapₐ ((Ideal.span {π ^ 4}).map (algebraMap R L))
          (Algebra.ofId R L) Ideal.le_comap_map).comp ρ) :
    ∃ (D : Type (max u w t)) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧
        ∃ (α : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] D)
          (β : D →ₐ[R] L), β.comp α = φ := by
  obtain ⟨B, _, _, hB, J, _hJfg, hJ, hrel, α, β, hβα⟩ :=
    exists_residual_quotient_factorization_of_quotient_section
      π f h hminor hrelations hπ hstableL ρ φ hcompat
  have : Smooth R B := hB
  have hcontrol : ∀ x : R, π ^ 2 * x = 0 → 1 * π * x = 0 := by
    simpa only [one_mul] using hstableR
  obtain ⟨D, _, _, hD, γ, δ, hδγ⟩ :=
    exists_smooth_factorization_of_residual_quotient π 1 hcontrol hπ
      (by simpa only [map_one] using (isUnit_one : IsUnit (1 : L))) J hJ hrel α β
  exact ⟨D, inferInstance, inferInstance, hD, γ, δ, hδγ.trans hβα⟩

end Algebra

namespace Algebra

open MvPolynomial

/-- The required power is constructed from the two Noetherian rings.
Every actual section modulo that power, compatible with the original target
map, then gives an exact smooth factorization. The section itself supplies
all approximate-coordinate data. -/
theorem exists_power_smooth_factorization_of_quotient_sections
    {R : Type u} {L : Type v} {m n k : Type w}
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
      ∀ (ρ : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
          R ⧸ Ideal.span {(π ^ N) ^ 4})
        (φ : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L),
        (Ideal.Quotient.mkₐ R
            ((Ideal.span {(π ^ N) ^ 4}).map (algebraMap R L))).comp φ =
          (Ideal.quotientMapₐ ((Ideal.span {(π ^ N) ^ 4}).map (algebraMap R L))
            (Algebra.ofId R L) Ideal.le_comap_map).comp ρ →
      ∃ (D : Type (max u w)) (_ : CommRing D) (_ : Algebra R D),
        Smooth R D ∧
          ∃ (α : (MvPolynomial n R ⧸
              (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] D)
            (β : D →ₐ[R] L), β.comp α = φ := by
  classical
  obtain ⟨N, hpos, hN⟩ := exists_power_smooth_factorization_of_strictStandard_data
    (L := L) π f h hminor hrelations hπ
  refine ⟨N, hpos, ?_⟩
  intro ρ φ hcompat
  obtain ⟨a, ha, hcoordinates⟩ := exists_coordinates_of_quotient_section
    (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ((π ^ N) ^ 4)
      ρ φ hcompat
  choose zeta hzeta using hcoordinates
  have hf (j : m) : (π ^ N) ^ 4 ∣ aeval a (f j) :=
    ha _ ((show Ideal.span (Set.range f) ≤
      Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h) from le_sup_left)
        (Ideal.subset_span (Set.mem_range_self j)))
  have hh (j : k) : (π ^ N) ^ 4 ∣ aeval a (h j) :=
    ha _ ((show Ideal.span (Set.range h) ≤
      Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h) from le_sup_right)
        (Ideal.subset_span (Set.mem_range_self j)))
  apply hN a hf hh φ zeta
  intro i
  simpa only [map_pow] using hzeta i

end Algebra
