/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.CubicCorrectionSmoothFactorization
public import Nyll.SchemeTheory.RingTheory.Smooth.ResidualRelationFactorization
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.FiniteType

/-!
# Cubic correction with the original residual relations

The original finite polynomial presentation is split into the relations
used by the scaled Jacobian and the remaining relations. The correction
construction retains coordinate divisibility in its actual smooth algebra.
Mapping the original relation-ideal memberships constructs the residual ideal
and its two parameter bounds. The first factorization retains that quotient,
without a controlling target unit. The existing smooth endpoint then removes
the residual ideal by the determinant trick. Both retain the original map.
-/

@[expose] public section

noncomputable section

universe u v w t z

open MvPolynomial
open scoped Matrix

namespace Algebra

/-- Cubic correction constructs a smooth algebra and retains its actual
residual quotient. Its finitely generated residual ideal satisfies both
parameter bounds, and the quotient factorization recovers the original map.
No controlling base element or unit condition is needed for this construction. -/
theorem exists_residual_quotient_factorization_of_general_cubic_correction_data
    {R : Type u} {L : Type v} {m : Type w} {n : Type t} {k : Type z}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [Finite m] [Fintype n] [DecidableEq m]
    (π u : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (S : Matrix n m R)
    (hS : Matrix.of (fun j i => constantCoeff (pderiv i (f j))) * S =
      (u * π) • (1 : Matrix m m R))
    (hu : π ∣ u - 1)
    (hf : ∀ j, π ^ 4 ∣ constantCoeff (f j))
    (hh : ∀ j, π ^ 4 ∣ constantCoeff (h j))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstable : ∀ x : L,
      algebraMap R L π ^ 2 * x = 0 → algebraMap R L π * x = 0)
    (φ : (MvPolynomial n R ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L)
    (zeta : n → L)
    (hzeta : ∀ i, φ (Ideal.Quotient.mk
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i)) =
      algebraMap R L π ^ 4 * zeta i) :
    ∃ (B : Type (max u w t)) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ J : Ideal B,
        J.FG ∧ J ≤ Ideal.span {algebraMap R B π ^ 2} ∧
        Ideal.span {algebraMap R B π} * J ≤ J ^ 2 ∧
        ∃ (α : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] B ⧸ J)
          (β : B ⧸ J →ₐ[R] L), β.comp α = φ := by
  classical
  let If : Ideal (MvPolynomial n R) := Ideal.span (Set.range f)
  let Ih : Ideal (MvPolynomial n R) := Ideal.span (Set.range h)
  let qf : MvPolynomial n R →ₐ[R] (MvPolynomial n R ⧸ If) :=
    Ideal.Quotient.mkₐ R If
  let qall : MvPolynomial n R →ₐ[R] (MvPolynomial n R ⧸ (If ⊔ Ih)) :=
    Ideal.Quotient.mkₐ R (If ⊔ Ih)
  let a : (MvPolynomial n R ⧸ If) →ₐ[R] (MvPolynomial n R ⧸ (If ⊔ Ih)) :=
    Ideal.Quotient.factorₐ R le_sup_left
  have haq : a.comp qf = qall := Ideal.Quotient.factorₐ_comp_mk R le_sup_left
  obtain ⟨B, _, _, hB, αf, β, hβαf, hcoordinates⟩ :=
    exists_smooth_factorization_of_cubic_correction_data_with_coordinates
      π u f S hS hu hf hπ hstable (φ.comp a) zeta hzeta
  have : Smooth R B := hB
  have : IsNoetherianRing B := FiniteType.isNoetherianRing R B
  let θ : MvPolynomial n R →ₐ[R] B := αf.comp qf
  have hθf (j : m) : θ (f j) = 0 := by
    change αf (Ideal.Quotient.mk If (f j)) = 0
    rw [Ideal.Quotient.mk_span_range, map_zero]
  have hIfker : If ≤ RingHom.ker θ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hθf j
  have hmapIf : Ideal.map θ.toRingHom If = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker θ.toRingHom).mpr hIfker
  let J : Ideal B := Ideal.span (Set.range (fun j => θ (h j)))
  have hmapIh : Ideal.map θ.toRingHom Ih = J := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hmapAll : Ideal.map θ.toRingHom (If ⊔ Ih) = J := by
    rw [Ideal.map_sup, hmapIf, hmapIh, bot_sup_eq]
  let Iπ : Ideal B := Ideal.span {algebraMap R B π ^ 2}
  let qπ : B →ₐ[R] B ⧸ Iπ := Ideal.Quotient.mkₐ R Iπ
  have hqθ : qπ.comp θ = aeval (fun _ : n => (0 : B ⧸ Iπ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [aeval_X]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcoordinates i)
  have hJ : J ≤ Iπ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hconstant : algebraMap R B (constantCoeff (h j)) ∈ Iπ := by
      obtain ⟨c, hc⟩ := hh j
      apply Ideal.mem_span_singleton.mpr
      refine ⟨algebraMap R B π ^ 2 * algebraMap R B c, ?_⟩
      rw [hc, map_mul, map_pow]
      ring
    have hc : qπ (algebraMap R B (constantCoeff (h j))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hconstant
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (qπ.comp θ) (h j) = 0
    rw [hqθ, aeval_zero']
    rw [qπ.commutes] at hc
    exact hc
  have hrelJ (j : k) : algebraMap R B π * θ (h j) ∈ J ^ 2 := by
    have hj := Ideal.mem_map_of_mem θ.toRingHom (hrelations j)
    rw [Ideal.map_sup, hmapIf, Ideal.map_pow, hmapAll, bot_sup_eq] at hj
    change θ (C π * h j) ∈ J ^ 2 at hj
    have hθπ : θ (C π) = algebraMap R B π := θ.commutes π
    rw [map_mul, hθπ] at hj
    exact hj
  have hrel : Ideal.span {algebraMap R B π} * J ≤ J ^ 2 := by
    change Ideal.span {algebraMap R B π} *
      Ideal.span (Set.range (fun j => θ (h j))) ≤ J ^ 2
    rw [Ideal.span_mul_span, Ideal.span_le]
    rintro _ ⟨x, hx, y, ⟨j, rfl⟩, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hrelJ j
  let qJ : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  let γ : MvPolynomial n R →ₐ[R] B ⧸ J := qJ.comp θ
  have hγker : If ⊔ Ih ≤ RingHom.ker γ.toRingHom := by
    apply sup_le
    · intro p hp
      change qJ (θ p) = 0
      rw [show θ p = 0 from hIfker hp, map_zero]
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change qJ (θ (h j)) = 0
      exact Ideal.Quotient.mk_span_range _ j
  let α : (MvPolynomial n R ⧸ (If ⊔ Ih)) →ₐ[R] B ⧸ J :=
    Ideal.Quotient.liftₐ (If ⊔ Ih) γ (fun p hp => hγker hp)
  have hα : α.comp qall = γ := Ideal.Quotient.liftₐ_comp _ _ _
  have hβθ : β.comp θ = φ.comp qall := by
    change β.comp (αf.comp qf) = φ.comp qall
    rw [← AlgHom.comp_assoc, hβαf, AlgHom.comp_assoc, haq]
  have hJker : J ≤ RingHom.ker β.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change (β.comp θ) (h j) = 0
    rw [hβθ]
    change φ (Ideal.Quotient.mk (If ⊔ Ih) (h j)) = 0
    have hj : Ideal.Quotient.mk (If ⊔ Ih) (h j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ih ≤ If ⊔ Ih from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self j)))
    rw [hj, map_zero]
  let βJ : B ⧸ J →ₐ[R] L := Ideal.Quotient.liftₐ J β (fun b hb => hJker hb)
  have hβJ : βJ.comp qJ = β := Ideal.Quotient.liftₐ_comp _ _ _
  refine ⟨B, inferInstance, inferInstance, hB, J, IsNoetherian.noetherian J,
    hJ, hrel, α, βJ, ?_⟩
  apply Ideal.Quotient.algHom_ext
  change (βJ.comp α).comp qall = φ.comp qall
  rw [AlgHom.comp_assoc, hα]
  change βJ.comp (qJ.comp θ) = φ.comp qall
  rw [← AlgHom.comp_assoc, hβJ]
  exact hβθ

/-- A constructed residual quotient factors through a smooth principal
localization when its controlling element is a unit in the original target. -/
theorem exists_smooth_factorization_of_residual_quotient
    {R : Type u} {A : Type v} {B : Type w} {L : Type t}
    [CommRing R] [CommRing A] [CommRing B] [CommRing L]
    [Algebra R A] [Algebra R B] [Algebra R L]
    [IsNoetherianRing R] [Smooth R B] [IsLocalRing L]
    (π r : R) (hcontrol : ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hr : IsUnit (algebraMap R L r))
    (J : Ideal B) (hJ : J ≤ Ideal.span {algebraMap R B π ^ 2})
    (hrel : Ideal.span {algebraMap R B π} * J ≤ J ^ 2)
    (α : A →ₐ[R] B ⧸ J) (β : B ⧸ J →ₐ[R] L) :
    ∃ (D : Type w) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (γ : A →ₐ[R] D) (δ : D →ₐ[R] L),
        δ.comp γ = β.comp α := by
  have : IsNoetherianRing B := FiniteType.isNoetherianRing R B
  let qJ : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  obtain ⟨s, αJ, δ, hαJ, hδ⟩ :=
    exists_localization_factorization_of_residual_ideal
      π r hcontrol (β.comp qJ) hπ hr J hJ hrel
  have hδJ : δ.comp αJ = β := by
    apply Ideal.Quotient.algHom_ext
    change (δ.comp αJ).comp qJ = β.comp qJ
    rw [AlgHom.comp_assoc, hαJ]
    exact hδ
  have : Smooth B (Localization.Away s) := Smooth.of_isLocalization_Away s
  have : Smooth R (Localization.Away s) := Smooth.comp R B (Localization.Away s)
  refine ⟨Localization.Away s, inferInstance, inferInstance, inferInstance,
    αJ.comp α, δ, ?_⟩
  rw [← AlgHom.comp_assoc, hδJ]

/-- The local-target case of the general desingularization calculation:
the remaining relations are removed using their original ideal memberships
and a controlling element of the base annihilator quotient whose target
image is a unit. No smooth algebra or relation-vanishing lift is an input. -/
theorem exists_smooth_factorization_of_general_cubic_correction_data
    {R : Type u} {L : Type v} {m : Type w} {n : Type t} {k : Type z}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [Finite m] [Fintype n] [DecidableEq m]
    (π u r : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (S : Matrix n m R)
    (hS : Matrix.of (fun j i => constantCoeff (pderiv i (f j))) * S =
      (u * π) • (1 : Matrix m m R))
    (hu : π ∣ u - 1)
    (hf : ∀ j, π ^ 4 ∣ constantCoeff (f j))
    (hh : ∀ j, π ^ 4 ∣ constantCoeff (h j))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hstable : ∀ x : L,
      algebraMap R L π ^ 2 * x = 0 → algebraMap R L π * x = 0)
    (hcontrol : ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0)
    (hr : IsUnit (algebraMap R L r))
    (φ : (MvPolynomial n R ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L)
    (zeta : n → L)
    (hzeta : ∀ i, φ (Ideal.Quotient.mk
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i)) =
      algebraMap R L π ^ 4 * zeta i) :
    ∃ (D : Type (max u w t)) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧
        ∃ (α : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] D)
          (β : D →ₐ[R] L), β.comp α = φ := by
  obtain ⟨B, _, _, hB, J, _hJfg, hJ, hrel, α, β, hβα⟩ :=
    exists_residual_quotient_factorization_of_general_cubic_correction_data
      π u f h S hS hu hf hh hrelations hπ hstable φ zeta hzeta
  have : Smooth R B := hB
  obtain ⟨D, _, _, hD, γ, δ, hδγ⟩ :=
    exists_smooth_factorization_of_residual_quotient π r hcontrol hπ hr J hJ hrel α β
  exact ⟨D, inferInstance, inferInstance, hD, γ, δ, hδγ.trans hβα⟩

end Algebra
