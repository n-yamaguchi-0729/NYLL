/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.ResidualRelationFactorization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# An actual annihilator controller outside a flat prime

Base annihilator stability transfers to the flat localization of the
intermediate algebra. Its annihilator of the parameter squared is finitely
generated, so one denominator outside the prime clears every localized
annihilation equation. This is the local controlling-element step in the
proof of Stacks 07CT; no global flatness of the intermediate algebra is used.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

private theorem exists_common_annihilator_of_fg_of_localization
    {D T : Type*} [CommRing D] [CommRing T] [Algebra D T]
    (M : Submonoid D) [IsLocalization M T]
    (K : Submodule D D) (hK : K.FG) (b : D)
    (hzero : ∀ x ∈ K, algebraMap D T (b * x) = 0) :
    ∃ r : M, ∀ x ∈ K, (r : D) * b * x = 0 := by
  classical
  obtain ⟨t, ht⟩ := hK
  have hex (i : ↥t) : ∃ s : M, (s : D) * (b * (i : D)) = 0 := by
    apply (IsLocalization.map_eq_zero_iff M T _).mp
    exact hzero i (ht ▸ Submodule.subset_span i.property)
  choose s hs using hex
  let r : M := ∏ i : ↥t, s i
  refine ⟨r, ?_⟩
  have hle : K ≤ LinearMap.ker (LinearMap.mulLeft D ((r : D) * b)) := by
    rw [← ht]
    apply Submodule.span_le.mpr
    intro x hx
    let i : ↥t := ⟨x, hx⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ i)
    change (r : D) * b * x = 0
    have hr : r = s i * c := hc
    rw [hr]
    change ((s i : D) * (c : D)) * b * x = 0
    calc
      ((s i : D) * (c : D)) * b * x =
          (c : D) * ((s i : D) * (b * (i : D))) := by
        change ((s i : D) * (c : D)) * b * x =
          (c : D) * ((s i : D) * (b * x))
        ring
      _ = 0 := by rw [hs i, mul_zero]
  intro x hx
  exact hle hx

namespace Algebra

/-- A flat localization supplies a controlling element outside the prime.
The element is constructed from the original base stability and the finite
annihilator module of the intermediate algebra. -/
theorem exists_annihilator_control_notMem_of_flat_atPrime
    {R D : Type*} [CommRing R] [CommRing D] [Algebra R D]
    [IsNoetherianRing D] (π : R)
    (hstable : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (p : Ideal D) [p.IsPrime] [Module.Flat R (Localization.AtPrime p)] :
    ∃ r : D, r ∉ p ∧ ∀ x : D,
      algebraMap R D π ^ 2 * x = 0 → r * algebraMap R D π * x = 0 := by
  let T := Localization.AtPrime p
  let b : D := algebraMap R D π
  let K : Submodule D D := LinearMap.ker (LinearMap.mulLeft D (b ^ 2))
  have hcontrol : ∀ x : R, π ^ 2 * x = 0 → 1 * π * x = 0 := by
    intro x hx
    rw [one_mul]
    exact hstable x hx
  have hzero (x : D) (hx : x ∈ K) : algebraMap D T (b * x) = 0 := by
    have hx0 : b ^ 2 * x = 0 := hx
    have hxT : algebraMap R T π ^ 2 * algebraMap D T x = 0 := by
      rw [IsScalarTower.algebraMap_apply R D T, ← map_pow, ← map_mul, hx0, map_zero]
    have hz := annihilator_control_of_flat π 1 hcontrol (algebraMap D T x) hxT
    rw [map_one, one_mul, IsScalarTower.algebraMap_apply R D T, ← map_mul] at hz
    exact hz
  obtain ⟨r, hr⟩ := exists_common_annihilator_of_fg_of_localization
    (T := T) p.primeCompl K (IsNoetherian.noetherian K) b hzero
  refine ⟨r, r.property, ?_⟩
  intro x hx
  exact hr x hx

end Algebra
