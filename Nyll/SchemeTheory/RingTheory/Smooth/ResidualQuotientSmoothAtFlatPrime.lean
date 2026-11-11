/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.AnnihilatorControlAtFlatPrime
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Smoothness of the actual residual quotient over a flat prime

The residual ideal vanishes in the relevant localization of the smooth
core. At primes containing the parameter this uses a constructed local
annihilator controller. Away from the parameter its mapped ideal is
idempotent, so local Nakayama kills it. The native quotient localization
is therefore a localization of the smooth core itself.
-/

@[expose] public section

noncomputable section

namespace Algebra

private theorem isSmoothAt_quotient_of_localized_kernel_zero
    {D B : Type*} [CommRing D] [CommRing B] [Algebra D B] [Smooth D B]
    (J : Ideal B) (q : Ideal (B ⧸ J)) [q.IsPrime]
    (hzero : ∀ x ∈ J,
      algebraMap B (Localization.AtPrime (q.comap (Ideal.Quotient.mk J))) x = 0) :
    IsSmoothAt D q := by
  let p : Ideal B := q.comap (Ideal.Quotient.mk J)
  let T := Localization.AtPrime p
  let f : B ⧸ J →ₐ[D] T :=
    Ideal.Quotient.liftₐ J (IsScalarTower.toAlgHom D B T) hzero
  let _ : Algebra (B ⧸ J) T := f.toRingHom.toAlgebra
  have : IsScalarTower D (B ⧸ J) T :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hM : p.primeCompl.map (Ideal.Quotient.mk J) = q.primeCompl := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨b, hx, rfl⟩
  have hloc : IsLocalization (p.primeCompl.map (Ideal.Quotient.mk J)) T :=
    IsLocalization.of_surjective p.primeCompl T
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (RingHom.id T) Function.surjective_id rfl (by
        intro x hx
        change x = 0 at hx
        rw [hx]
        exact Ideal.zero_mem _)
  have : IsLocalization q.primeCompl T := hM ▸ hloc
  have : FormallySmooth D T := inferInstance
  exact FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).restrictScalars D)

private theorem residual_ideal_zero_atPrime_of_control
    {D B : Type*} [CommRing D] [CommRing B] [Algebra D B]
    [IsNoetherianRing D] [Smooth D B]
    (π r : D) (hcontrol : ∀ x : D, π ^ 2 * x = 0 → r * π * x = 0)
    (J : Ideal B) (hJ : J ≤ Ideal.span {algebraMap D B π ^ 2})
    (hrel : Ideal.span {algebraMap D B π} * J ≤ J ^ 2)
    (p : Ideal B) [p.IsPrime] (hJp : J ≤ p) (hr : algebraMap D B r ∉ p) :
    ∀ x ∈ J, algebraMap B (Localization.AtPrime p) x = 0 := by
  classical
  have : IsNoetherianRing B := FiniteType.isNoetherianRing D B
  let T := Localization.AtPrime p
  by_cases hπ : algebraMap D B π ∈ p
  · have hπT : algebraMap D T π ∈ IsLocalRing.maximalIdeal T := by
      rw [IsScalarTower.algebraMap_apply D B T]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T p _).mpr hπ
    have hrT : IsUnit (algebraMap D T r) := by
      rw [IsScalarTower.algebraMap_apply D B T]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff T p _).mpr hr
    obtain ⟨s, hs, hkill⟩ := exists_target_unit_annihilating_residual_ideal
      π r hcontrol (IsScalarTower.toAlgHom D B T) hπT hrT J hJ hrel
    intro x hx
    have heq := congrArg (algebraMap B T) (hkill x hx)
    rw [map_mul, map_zero] at heq
    exact hs.mul_right_eq_zero.mp heq
  · let K : Ideal T := J.map (algebraMap B T)
    have hKmax : K ≤ IsLocalRing.maximalIdeal T := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T p x).mpr (hJp hx)
    have hKrel : Ideal.span {algebraMap D T π} * K ≤ K ^ 2 := by
      have hm := Ideal.map_mono (f := algebraMap B T) hrel
      rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hm
      change Ideal.span {algebraMap B T (algebraMap D B π)} * K ≤ K ^ 2 at hm
      simpa only [← IsScalarTower.algebraMap_apply D B T] using hm
    have hunit : IsUnit (algebraMap D T π) := by
      rw [IsScalarTower.algebraMap_apply D B T]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff T p _).mpr hπ
    have htop : Ideal.span {algebraMap D T π} = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hunit
    have hKK : K ≤ K • K := by
      change K ≤ K * K
      simpa only [htop, Ideal.top_mul, pow_two] using hKrel
    obtain ⟨s, hs, hkill⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
        K K (IsNoetherian.noetherian K) hKK
    have hsunit : IsUnit s := by
      apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
      change 1 - s ∈ IsLocalRing.maximalIdeal T
      simpa only [neg_sub] using (IsLocalRing.maximalIdeal T).neg_mem (hKmax hs)
    intro x hx
    exact hsunit.mul_right_eq_zero.mp
      (hkill _ (Ideal.mem_map_of_mem (algebraMap B T) hx))

/-- Residual correction preserves smoothness over every flat prime of the
intermediate algebra. All controlling elements are constructed from base
annihilator stability; the intermediate algebra need not be flat globally. -/
theorem isSmoothAt_residualQuotient_of_flat_atPrime
    {R D B : Type*} [CommRing R] [CommRing D] [CommRing B]
    [Algebra R D] [Algebra D B] [Algebra R B] [IsScalarTower R D B]
    [IsNoetherianRing D] [Smooth D B]
    (π : R) (hstable : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (J : Ideal B) (hJ : J ≤ Ideal.span {algebraMap R B π ^ 2})
    (hrel : Ideal.span {algebraMap R B π} * J ≤ J ^ 2)
    (q : Ideal (B ⧸ J)) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime (q.comap (algebraMap D (B ⧸ J))))] :
    IsSmoothAt D q := by
  let pD : Ideal D := q.comap (algebraMap D (B ⧸ J))
  let pB : Ideal B := q.comap (Ideal.Quotient.mk J)
  obtain ⟨r, hr, hcontrol⟩ :=
    exists_annihilator_control_notMem_of_flat_atPrime π hstable pD
  have hJp : J ≤ pB := by
    intro x hx
    change Ideal.Quotient.mk J x ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.zero_mem
  have hrB : algebraMap D B r ∉ pB := by
    intro h
    apply hr
    change Ideal.Quotient.mk J (algebraMap D B r) ∈ q at h
    exact h
  have hJD : J ≤ Ideal.span {algebraMap D B (algebraMap R D π) ^ 2} := by
    simpa only [← IsScalarTower.algebraMap_apply R D B] using hJ
  have hrelD : Ideal.span {algebraMap D B (algebraMap R D π)} * J ≤ J ^ 2 := by
    simpa only [← IsScalarTower.algebraMap_apply R D B] using hrel
  exact isSmoothAt_quotient_of_localized_kernel_zero J q
    (residual_ideal_zero_atPrime_of_control (algebraMap R D π) r hcontrol
      J hJD hrelD pB hJp hrB)

end Algebra
