/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SmoothFactorizationAtApproximateSection
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Powering the original strictly-standard presentation data

The power is chosen from the actual increasing chains of annihilators in
the two Noetherian rings. The original polynomial minor membership and
residual-relation memberships are then powered and evaluated at an actual
approximate section. This supplies every matrix and annihilator input of
the correction construction and retains the original algebra map.
-/

@[expose] public section

noncomputable section

universe u v w t z

open MvPolynomial
open scoped Matrix

namespace Algebra

/-- Multiplication by a sufficiently high power has a stable annihilator. -/
theorem eventually_annihilator_pow_stable
    {R : Type*} [CommRing R] [IsNoetherianRing R] (π : R) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ x : R,
      (π ^ N) ^ 2 * x = 0 → π ^ N * x = 0 := by
  refine (LinearMap.eventually_iSup_ker_pow_eq (LinearMap.mulLeft R π)).mono ?_
  intro N hN x hx
  have hx' : x ∈ LinearMap.ker ((LinearMap.mulLeft R π) ^ (N * 2)) := by
    rw [LinearMap.mem_ker, LinearMap.pow_mulLeft]
    change π ^ (N * 2) * x = 0
    simpa only [pow_mul] using hx
  have hx'' : x ∈ ⨆ j : ℕ, LinearMap.ker ((LinearMap.mulLeft R π) ^ j) :=
    (le_iSup (fun j : ℕ => LinearMap.ker ((LinearMap.mulLeft R π) ^ j)) (N * 2)) hx'
  rw [hN] at hx''
  simpa only [LinearMap.mem_ker, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply] using hx''

/-- A positive power of an original strictly-standard parameter can be chosen
so that every actual fourth-order approximate section for that power gives a
smooth factorization of the original map. The power, scaled Jacobian inverse,
and both annihilator controls are constructed, rather than supplied. -/
theorem exists_power_smooth_factorization_of_strictStandard_data
    {R : Type u} {L : Type v} {m : Type w} {n : Type t} {k : Type z}
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
      ∀ (a : n → R)
        (_ : ∀ j, (π ^ N) ^ 4 ∣ aeval a (f j))
        (_ : ∀ j, (π ^ N) ^ 4 ∣ aeval a (h j))
        (φ : (MvPolynomial n R ⧸
          (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L)
        (zeta : n → L)
        (_ : ∀ i, φ (Ideal.Quotient.mk
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i)) -
            algebraMap R L (a i) = algebraMap R L (π ^ N) ^ 4 * zeta i),
      ∃ (D : Type (max u w t)) (_ : CommRing D) (_ : Algebra R D),
        Smooth R D ∧
          ∃ (α : (MvPolynomial n R ⧸
              (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] D)
            (β : D →ₐ[R] L), β.comp α = φ := by
  classical
  let _ : Fintype n := Fintype.ofFinite n
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    ((eventually_annihilator_pow_stable π).and
      (eventually_annihilator_pow_stable (algebraMap R L π)))
  refine ⟨b + 1, Nat.zero_lt_succ b, ?_⟩
  intro a hf hh φ zeta hzeta
  let If : Ideal (MvPolynomial n R) := Ideal.span (Set.range f)
  let Ih : Ideal (MvPolynomial n R) := Ideal.span (Set.range h)
  let J : Ideal (MvPolynomial n R) := Ideal.span (Set.range fun c : m → n =>
    ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det)
  let K : Ideal R := Ideal.span {(π ^ (b + 1)) ^ 4}
  let M : Matrix m n R := Matrix.of fun j i => aeval a (pderiv i (f j))
  let J₀ : Ideal R := Ideal.span (Set.range fun c : m → n => (M.submatrix _root_.id c).det)
  let e : MvPolynomial n R →+* R := (aeval a).toRingHom
  have hpowered : C (π ^ (b + 1)) ∈ (If ⊔ Ih) ⊔ J := by
    rw [map_pow, pow_succ]
    exact ((If ⊔ Ih) ⊔ J).mul_mem_left _ hminor
  have heIf : Ideal.map e If ≤ K := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_span_singleton.mpr (hf j)
  have heIh : Ideal.map e Ih ≤ K := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_span_singleton.mpr (hh j)
  have heJ : Ideal.map e J ≤ J₀ := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change e (((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det) ∈ J₀
    rw [RingHom.map_det]
    exact Ideal.subset_span (Set.mem_range_self c)
  have heAll : Ideal.map e ((If ⊔ Ih) ⊔ J) ≤ K ⊔ J₀ := by
    rw [Ideal.map_sup, Ideal.map_sup]
    exact sup_le_sup (sup_le heIf heIh) heJ
  have hminor' : π ^ (b + 1) ∈ J₀ ⊔ K := by
    have hp := heAll (Ideal.mem_map_of_mem e hpowered)
    change aeval a (C (π ^ (b + 1))) ∈ K ⊔ J₀ at hp
    rw [aeval_C, Algebra.algebraMap_self_apply] at hp
    simpa only [sup_comm] using hp
  have hrelations' (j : k) : C (π ^ (b + 1)) * h j ∈ If ⊔ (If ⊔ Ih) ^ 2 := by
    have hj := (If ⊔ (If ⊔ Ih) ^ 2).mul_mem_left ((C π) ^ b) (hrelations j)
    rw [map_pow, pow_succ (C π) b, mul_assoc]
    exact hj
  have hπ' : algebraMap R L (π ^ (b + 1)) ∈ IsLocalRing.maximalIdeal L := by
    rw [map_pow, pow_succ]
    exact (IsLocalRing.maximalIdeal L).mul_mem_left _ hπ
  obtain ⟨hR, hL⟩ := hb (b + 1) (Nat.le_succ b)
  have hstable : ∀ x : L,
      algebraMap R L (π ^ (b + 1)) ^ 2 * x = 0 →
        algebraMap R L (π ^ (b + 1)) * x = 0 := by
    simpa only [map_pow] using hL
  have hcontrol : ∀ x : R,
      (π ^ (b + 1)) ^ 2 * x = 0 → 1 * π ^ (b + 1) * x = 0 := by
    simpa only [one_mul] using hR
  exact exists_smooth_factorization_at_approximate_section
    (π ^ (b + 1)) 1 f h a hminor' hf hh hrelations' hπ' hstable hcontrol
    (by simpa only [map_one] using (isUnit_one : IsUnit (1 : L))) φ zeta hzeta

end Algebra
