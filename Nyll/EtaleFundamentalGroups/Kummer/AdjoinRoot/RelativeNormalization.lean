/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootDivisor
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Ring

/-!
# Relative normalization of a standard root cover

A ring whose principal Cartier divisor is reduced is integrally closed in
its localization away from that divisor. This is proved directly: lying-over
forces the numerator of an integral fraction to belong to every prime above
the divisor; radicality cancels one denominator, and induction cancels all
remaining powers. Neither normality of the ambient ring nor of its boundary
localizations is assumed.

Applied to the actual root algebra, this identifies the algebra itself as
the integral closure of the original base inside the literal away algebra.
This supplies the affine relative-normalization step used by Stacks Project,
Lemma 58.31.6, on its standard charts. It does not assert the global étale
chart construction or descent of the resulting normalization.
https://stacks.math.columbia.edu/tag/0BSE
-/

noncomputable section

open Polynomial

universe u v

namespace EtaleFundamentalGroups.Kummer

/-- A radical principal ideal contracts through an integral element:
if `d * y` lies in the base and `y` is integral, its numerator is divisible
by `d` in the base. Lying-over supplies every prime needed for radicality. -/
private theorem dvd_of_integral_mul_eq_of_radical
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    (hinj : Function.Injective (algebraMap R T))
    (d : R) (hrad : (Ideal.span ({d} : Set R)).IsRadical)
    {y : T} (hy : IsIntegral R y) {a : R}
    (hda : algebraMap R T d * y = algebraMap R T a) : d ∣ a := by
  let S := integralClosure R T
  have hinjS : Function.Injective (algebraMap R S) := by
    intro r s h
    apply hinj
    exact congrArg (fun z : S => (z : T)) h
  apply Ideal.mem_span_singleton.mp
  apply hrad
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  change ∀ p : Ideal R, Ideal.span ({d} : Set R) ≤ p ∧ p.IsPrime → a ∈ p
  intro p hp
  have : p.IsPrime := hp.2
  have hker : (⊥ : Ideal S).under R ≤ p := by
    intro r hr
    have hz : algebraMap R S r = 0 := hr
    have hrzero : r = 0 := hinjS (hz.trans (map_zero (algebraMap R S)).symm)
    exact hrzero ▸ p.zero_mem
  obtain ⟨q, _, _, hqp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := S) p ⊥ hker
  have hdq : algebraMap R S d ∈ q := by
    change d ∈ q.under R
    rw [hqp]
    exact hp.1 (Ideal.mem_span_singleton_self d)
  have hm : algebraMap R S d * (⟨y, hy⟩ : S) = algebraMap R S a := by
    apply Subtype.ext
    exact hda
  have haq : algebraMap R S a ∈ q := by
    rw [← hm]
    exact q.mul_mem_right (⟨y, hy⟩ : S) hdq
  change a ∈ p
  rw [← hqp]
  exact haq

/-- An integral fraction with denominator a power of a reduced Cartier
parameter already belongs to the original ring. -/
theorem isIntegrallyClosedIn_away_of_radical_principal
    {R : Type u} [CommRing R] (d : R) (hd : d ∈ nonZeroDivisors R)
    (hrad : (Ideal.span ({d} : Set R)).IsRadical)
    (T : Type v) [CommRing T] [Algebra R T] [IsLocalization.Away d T] :
    IsIntegrallyClosedIn R T := by
  have hinj : Function.Injective (algebraMap R T) :=
    IsLocalization.injective T (Submonoid.powers_le.mpr hd)
  refine isIntegrallyClosedIn_iff.mpr ⟨hinj, ?_⟩
  intro y hy
  have cancelDenominator (m : ℕ) : ∀ a : R,
      y * algebraMap R T d ^ m = algebraMap R T a →
        ∃ b : R, algebraMap R T b = y := by
    induction m with
    | zero =>
      intro a ha
      refine ⟨a, ?_⟩
      simpa only [pow_zero, mul_one] using ha.symm
    | succ m ih =>
      intro a ha
      have hyScaled : IsIntegral R (algebraMap R T d ^ m * y) := by
        rw [← map_pow]
        exact isIntegral_algebraMap.mul hy
      have hscaled : algebraMap R T d * (algebraMap R T d ^ m * y) =
          algebraMap R T a := by
        calc
          algebraMap R T d * (algebraMap R T d ^ m * y) =
              y * algebraMap R T d ^ (m + 1) := by
            rw [pow_succ]
            ring
          _ = algebraMap R T a := ha
      obtain ⟨b, hb⟩ := dvd_of_integral_mul_eq_of_radical hinj d hrad hyScaled hscaled
      apply ih b
      apply (IsLocalization.Away.algebraMap_isUnit (S := T) d).mul_left_cancel
      calc
        algebraMap R T d * (y * algebraMap R T d ^ m) =
            y * algebraMap R T d ^ (m + 1) := by
          rw [pow_succ]
          ring
        _ = algebraMap R T a := ha
        _ = algebraMap R T d * algebraMap R T b := by rw [hb, map_mul]
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj d y
  exact cancelDenominator m a ha

/-- The standard root algebra is the actual relative integral closure of
its base inside its own literal localization away from the radicand.
The assertion does not require the original ring to be a domain or normal. -/
theorem standardKummerCover_isIntegralClosure_away
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))] :
    let B := AdjoinRoot (X ^ n - C f)
    let T := Localization.Away (algebraMap A B f)
    IsIntegralClosure B A T := by
  intro B T
  let x : B := AdjoinRoot.root (X ^ n - C f)
  have hx : x ∈ nonZeroDivisors B := adjoinRoot_root_mem_nonZeroDivisors hn f hf
  have hxpow : x ^ n = algebraMap A B f := by
    rw [AdjoinRoot.algebraMap_eq]
    exact adjoinRoot_root_pow n f
  have hfB : algebraMap A B f ∈ nonZeroDivisors B :=
    hxpow ▸ pow_mem hx n
  have hinj : Function.Injective (algebraMap B T) :=
    IsLocalization.injective T (Submonoid.powers_le.mpr hfB)
  have hxUnit : IsUnit (algebraMap B T x) := by
    apply (isUnit_pow_iff hn.ne').mp
    rw [← map_pow, hxpow]
    exact IsLocalization.Away.algebraMap_isUnit (S := T) (algebraMap A B f)
  have hloc : IsLocalization.Away x T := IsLocalization.Away.mk x hxUnit
    (fun z => by
      obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj (algebraMap A B f) z
      refine ⟨n * m, b, ?_⟩
      rw [pow_mul, ← map_pow, hxpow]
      exact hb)
    (fun a b hab => ⟨0, by simpa only [pow_zero, one_mul] using hinj hab⟩)
  have hrad : (Ideal.span ({x} : Set B)).IsRadical :=
    (isRadical_span_adjoinRoot_root_iff_reduced_quotient hn f).mpr inferInstance
  have hclosed : IsIntegrallyClosedIn B T :=
    isIntegrallyClosedIn_away_of_radical_principal x hx hrad T
  have : Module.Finite A B := (Polynomial.monic_X_pow_sub_C f hn.ne').finite_adjoinRoot
  exact IsIntegralClosure.of_isIntegrallyClosedIn

end EtaleFundamentalGroups.Kummer
