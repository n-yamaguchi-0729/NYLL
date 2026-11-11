/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Removing the residual relation ideal in desingularization

The determinant trick constructs an element congruent to one modulo the
desingularization parameter which kills its product with the residual
relation ideal. Flatness transfers the original base annihilator relation;
this kills the residual ideal itself after one actual principal localization.
The localization retains the map to the original local target.
-/

@[expose] public section

noncomputable section

namespace Algebra

/-- A controlling element for the base annihilator quotient retains its
annihilation property in a flat algebra. The proof trivializes the actual
one-term relation by the equational criterion for flatness. -/
theorem annihilator_control_of_flat
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    (π r : R) (h : ∀ z : R, π ^ 2 * z = 0 → r * π * z = 0)
    (x : B) (hx : algebraMap R B π ^ 2 * x = 0) :
    algebraMap R B r * algebraMap R B π * x = 0 := by
  classical
  have hrel : ∑ _i : Unit, (π ^ 2) • x = 0 := by
    simpa only [Fintype.sum_unique, Algebra.smul_def, map_pow] using hx
  obtain ⟨m, c, y, hxy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have hc' (j : Fin m) : π ^ 2 * c () j = 0 := by
    simpa only [Fintype.sum_unique] using hc j
  have hxy' : x = ∑ j, c () j • y j := hxy ()
  rw [hxy']
  simp only [Algebra.smul_def]
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _hj
  calc
    algebraMap R B r * algebraMap R B π * (algebraMap R B (c () j) * y j) =
        algebraMap R B (r * π * c () j) * y j := by
      rw [map_mul, map_mul]
      ring
    _ = 0 := by rw [h _ (hc' j), map_zero, zero_mul]

/-- The actual residual ideal is annihilated by one element which is a
unit in the original local target. This is the Nakayama step of Stacks
07CR, retaining a controlling element for the base annihilator quotient. -/
theorem exists_target_unit_annihilating_residual_ideal
    {R B L : Type*} [CommRing R] [CommRing B] [CommRing L]
    [Algebra R B] [Algebra R L] [Module.Flat R B]
    [IsNoetherianRing B] [IsLocalRing L]
    (π r : R) (hcontrol : ∀ z : R, π ^ 2 * z = 0 → r * π * z = 0)
    (β : B →ₐ[R] L)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hr : IsUnit (algebraMap R L r))
    (J : Ideal B)
    (hJ : J ≤ Ideal.span {algebraMap R B π ^ 2})
    (hrel : Ideal.span {algebraMap R B π} * J ≤ J ^ 2) :
    ∃ s : B, IsUnit (β s) ∧ ∀ x ∈ J, s * x = 0 := by
  let b : B := algebraMap R B π
  let I : Ideal B := Ideal.span {b}
  let N : Ideal B := I * J
  have hNN : N ≤ I • N := by
    change I * J ≤ I * (I * J)
    calc
      I * J ≤ J ^ 2 := hrel
      _ ≤ Ideal.span {b ^ 2} * J := by
        rw [pow_two]
        exact Ideal.mul_mono_left hJ
      _ = I * (I * J) := by
        rw [← Ideal.span_singleton_pow, pow_two, mul_assoc]
  obtain ⟨u, hu, hkill⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      I N (IsNoetherian.noetherian N) hNN
  have hunitu : IsUnit (β u) := by
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hu
    have hm : β u - 1 ∈ IsLocalRing.maximalIdeal L := by
      rw [← map_one β, ← map_sub, hv, map_mul]
      rw [show β b = algebraMap R L π from β.commutes π]
      exact Ideal.mul_mem_right _ _ hπ
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    change 1 - β u ∈ IsLocalRing.maximalIdeal L
    simpa only [neg_sub] using (IsLocalRing.maximalIdeal L).neg_mem hm
  refine ⟨algebraMap R B r * u, ?_, ?_⟩
  · rw [map_mul, β.commutes]
    exact hr.mul hunitu
  · intro x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (hJ hx)
    have hbx : b * x ∈ N :=
      Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton b)) hx
    have hukill : u * (b * x) = 0 := hkill _ hbx
    have hzero : b ^ 2 * (u * b * y) = 0 := by
      calc
        b ^ 2 * (u * b * y) = u * (b * (b ^ 2 * y)) := by ring
        _ = u * (b * x) := by rw [← hy]
        _ = 0 := hukill
    have hc := annihilator_control_of_flat π r hcontrol (u * b * y) hzero
    calc
      (algebraMap R B r * u) * x =
          algebraMap R B r * b * (u * b * y) := by rw [hy]; ring
      _ = 0 := hc

/-- The residual quotient maps to an actual principal localization of the
original algebra. The localization keeps its original target map and the
quotient comparison is the native quotient map. Smoothness, when already
constructed for the correction algebra, is preserved by this localization. -/
theorem exists_localization_factorization_of_residual_ideal
    {R B L : Type*} [CommRing R] [CommRing B] [CommRing L]
    [Algebra R B] [Algebra R L] [Module.Flat R B]
    [IsNoetherianRing B] [IsLocalRing L]
    (π r : R) (hcontrol : ∀ z : R, π ^ 2 * z = 0 → r * π * z = 0)
    (β : B →ₐ[R] L)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hr : IsUnit (algebraMap R L r))
    (J : Ideal B)
    (hJ : J ≤ Ideal.span {algebraMap R B π ^ 2})
    (hrel : Ideal.span {algebraMap R B π} * J ≤ J ^ 2) :
    ∃ s : B, ∃ (α : B ⧸ J →ₐ[R] Localization.Away s)
      (δ : Localization.Away s →ₐ[R] L),
      α.comp (Ideal.Quotient.mkₐ R J) =
        IsScalarTower.toAlgHom R B (Localization.Away s) ∧
      δ.comp (IsScalarTower.toAlgHom R B (Localization.Away s)) = β := by
  obtain ⟨s, hs, hkill⟩ :=
    exists_target_unit_annihilating_residual_ideal π r hcontrol β hπ hr J hJ hrel
  let q : B →ₐ[R] Localization.Away s :=
    IsScalarTower.toAlgHom R B (Localization.Away s)
  have hq (x : B) (hx : x ∈ J) : q x = 0 := by
    have h := congrArg q (hkill x hx)
    rw [map_mul, map_zero] at h
    exact (IsLocalization.Away.algebraMap_isUnit s).mul_right_eq_zero.mp h
  let α : B ⧸ J →ₐ[R] Localization.Away s := Ideal.Quotient.liftₐ J q hq
  let δ : Localization.Away s →ₐ[R] L := IsLocalization.Away.liftAlgHom s hs
  refine ⟨s, α, δ, Ideal.Quotient.liftₐ_comp _ _ _, ?_⟩
  apply AlgHom.ext
  intro x
  exact IsLocalization.Away.lift_eq s hs x

end Algebra
