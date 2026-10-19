/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Ring

/-!
# Principal-unit layers of a nilpotent ideal

For `I² ≤ J`, the actual map `u ↦ u - 1 mod J` is a homomorphism from
the units congruent to one modulo `I` to the additive image of `I` in `R/J`.
For a nilpotent ideal it is surjective, with kernel precisely the units
congruent to one modulo `J`. Thus every positive successive layer of the
principal-unit filtration is an actual additive ideal layer. The filtration
terminates for every nilpotent ideal, including ideals in truncated algebras.
-/

noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Units congruent to one modulo an actual ideal. -/
def principalUnits (I : Ideal R) : Subgroup Rˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker

/-- The kernel definition retains full ideal membership. -/
theorem mem_principalUnits (I : Ideal R) (u : Rˣ) :
    u ∈ I.principalUnits ↔ (u : R) - 1 ∈ I := by
  change Units.map (Ideal.Quotient.mk I).toMonoidHom u = 1 ↔ _
  rw [← Units.val_inj]
  change Ideal.Quotient.mk I (u : R) = 1 ↔ _
  rw [← (Ideal.Quotient.mk I).map_one]
  exact Ideal.Quotient.eq

/-- Inclusion of ideals gives inclusion of their principal-unit subgroups. -/
theorem principalUnits_mono {I J : Ideal R} (h : I ≤ J) :
    I.principalUnits ≤ J.principalUnits := by
  intro u hu
  exact (J.mem_principalUnits u).mpr (h ((I.mem_principalUnits u).mp hu))

/-- Congruence modulo the zero ideal is the identity subgroup. -/
theorem principalUnits_bot : (⊥ : Ideal R).principalUnits = ⊥ := by
  ext u
  rw [mem_principalUnits, Ideal.mem_bot, sub_eq_zero, Subgroup.mem_bot]
  exact (Units.val_inj (a := u) (b := 1))

/-- Nilpotence of the ideal supplies nilpotence of every one of its elements. -/
theorem isNilpotent_element_of_mem {I : Ideal R} (hI : IsNilpotent I)
    {a : R} (ha : a ∈ I) : IsNilpotent a := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, ?_⟩
  have hmem := Ideal.pow_mem_pow ha N
  rw [hN] at hmem
  exact hmem

/-- The first-order map on actual principal units, with values in the actual
image ideal in the quotient ring. -/
def principalUnitLayerMap (I J : Ideal R) (hIJ : I ^ 2 ≤ J) :
    I.principalUnits →* Multiplicative (I.map (Ideal.Quotient.mk J)) where
  toFun u := Multiplicative.ofAdd
    ⟨Ideal.Quotient.mk J ((u.1 : R) - 1),
      Ideal.mem_map_of_mem _ ((I.mem_principalUnits u.1).mp u.2)⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change Ideal.Quotient.mk J ((1 : R) - 1) = 0
    rw [sub_self, map_zero]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change Ideal.Quotient.mk J ((u.1 : R) * (v.1 : R) - 1) =
      Ideal.Quotient.mk J ((u.1 : R) - 1) + Ideal.Quotient.mk J ((v.1 : R) - 1)
    have hprod : ((u.1 : R) - 1) * ((v.1 : R) - 1) ∈ J := by
      apply hIJ
      rw [pow_two]
      exact Ideal.mul_mem_mul ((I.mem_principalUnits u.1).mp u.2)
        ((I.mem_principalUnits v.1).mp v.2)
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hprod
    have he : (u.1 : R) * (v.1 : R) - 1 =
        ((u.1 : R) - 1) + ((v.1 : R) - 1) +
          ((u.1 : R) - 1) * ((v.1 : R) - 1) := by ring
    rw [he, map_add, map_add, hz, add_zero]

/-- The first-order map vanishes precisely at the next congruence level. -/
theorem principalUnitLayerMap_eq_one_iff (I J : Ideal R) (hIJ : I ^ 2 ≤ J)
    (u : I.principalUnits) :
    I.principalUnitLayerMap J hIJ u = 1 ↔ (u.1 : R) - 1 ∈ J := by
  change (⟨Ideal.Quotient.mk J ((u.1 : R) - 1), _⟩ : I.map (Ideal.Quotient.mk J)) = 0 ↔ _
  rw [Subtype.ext_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The kernel is the literal next principal-unit subgroup inside the previous one. -/
theorem principalUnitLayerMap_ker (I J : Ideal R) (hIJ : I ^ 2 ≤ J) :
    (I.principalUnitLayerMap J hIJ).ker = J.principalUnits.subgroupOf I.principalUnits := by
  ext u
  change I.principalUnitLayerMap J hIJ u = 1 ↔ u.1 ∈ J.principalUnits
  rw [principalUnitLayerMap_eq_one_iff, mem_principalUnits]

/-- Every additive layer element lifts to the actual unit `1 + a`; its
invertibility follows from nilpotence of the given ideal. -/
theorem principalUnitLayerMap_surjective (I J : Ideal R) (hI : IsNilpotent I)
    (hIJ : I ^ 2 ≤ J) : Function.Surjective (I.principalUnitLayerMap J hIJ) := by
  intro y
  obtain ⟨a, ha, hay⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).mp
      (Multiplicative.toAdd y).2
  have hunit := (isNilpotent_element_of_mem hI ha).isUnit_one_add
  let u : Rˣ := hunit.unit
  have hu : (u : R) = 1 + a := hunit.unit_spec
  have hmem : u ∈ I.principalUnits := by
    rw [mem_principalUnits, hu, add_sub_cancel_left]
    exact ha
  refine ⟨⟨u, hmem⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change Ideal.Quotient.mk J ((u : R) - 1) = (Multiplicative.toAdd y).1
  rw [hu, add_sub_cancel_left, hay]

/-- The actual principal-unit quotient is an additive ideal layer. -/
def principalUnitLayerEquiv (I J : Ideal R) (hI : IsNilpotent I) (hIJ : I ^ 2 ≤ J) :
    I.principalUnits ⧸ J.principalUnits.subgroupOf I.principalUnits ≃*
      Multiplicative (I.map (Ideal.Quotient.mk J)) :=
  QuotientGroup.liftEquiv _ (I.principalUnitLayerMap_surjective J hI hIJ)
    (I.principalUnitLayerMap_ker J hIJ).symm

/-- The quotient equivalence is exactly reduction of `u - 1`. -/
theorem principalUnitLayerEquiv_apply (I J : Ideal R) (hI : IsNilpotent I)
    (hIJ : I ^ 2 ≤ J) (u : I.principalUnits) :
    I.principalUnitLayerEquiv J hI hIJ (QuotientGroup.mk u) =
      I.principalUnitLayerMap J hIJ u := rfl

/-- The principal-unit filtration reverses powers of its defining ideal. -/
theorem principalUnits_pow_antitone (I : Ideal R) :
    Antitone (fun n : ℕ => (I ^ n).principalUnits) := by
  intro m n h
  exact principalUnits_mono (Ideal.pow_le_pow_right h)

/-- A nilpotent ideal gives a finite filtration ending at the identity. -/
theorem principalUnits_pow_eventually_bot (I : Ideal R) (hI : IsNilpotent I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (I ^ n).principalUnits = ⊥ := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, ?_⟩
  intro n hn
  have hpow : I ^ n = ⊥ := by
    apply le_bot_iff.mp
    have hle : I ^ n ≤ I ^ N := Ideal.pow_le_pow_right hn
    rw [hN] at hle
    exact hle
  rw [hpow, principalUnits_bot]

/-- Every positive principal-unit layer of a nilpotent ideal is the additive
image of `Iⁿ` in the actual quotient ring `R/Iⁿ⁺¹`. -/
def principalUnits_pow_succ_equiv (I : Ideal R) (hI : IsNilpotent I)
    (n : ℕ) (hn : 0 < n) :
    (I ^ n).principalUnits ⧸
        (I ^ (n + 1)).principalUnits.subgroupOf (I ^ n).principalUnits ≃*
      Multiplicative ((I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  have hnil : IsNilpotent (I ^ n) := by
    obtain ⟨N, hN⟩ := hI
    refine ⟨N, ?_⟩
    rw [← pow_mul, Nat.mul_comm n N, pow_mul, hN, zero_pow (Nat.ne_of_gt hn)]
  have hpow : (I ^ n) ^ 2 ≤ I ^ (n + 1) := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by omega)
  exact (I ^ n).principalUnitLayerEquiv (I ^ (n + 1)) hnil hpow

/-- The image ideal in any actual truncation is nilpotent to the original
truncation order. In particular this applies to `(t)/(tᴺ)` in a polynomial algebra. -/
theorem quotientPower_map_pow_eq_bot (I : Ideal R) (N : ℕ) :
    (I.map (Ideal.Quotient.mk (I ^ N))) ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

end Ideal
