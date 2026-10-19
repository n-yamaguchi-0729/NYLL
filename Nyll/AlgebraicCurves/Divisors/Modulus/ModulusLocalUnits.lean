/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core

/-!
# Truncated local units of a modulus

The local congruence subgroup is the actual kernel of reduction to the units
of the truncated valuation ring. Its definition is independent of a
uniformizer; the comparison with the existing higher-unit subgroup is proved
for every irreducible element of the valuation ring.

This is the local algebra in Serre, *Algebraic Groups and Class Fields*,
Chapter V, §3, no. 13–14. The unit reduction and first-isomorphism APIs come
from `Valuation.AbsoluteValue.Theory.Core`.
-/

noncomputable section

namespace AlgebraicCurve.Place

open LubinTate.Valuations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Local units whose image in the `n`-th truncated local ring is one. -/
def congruenceUnitSubgroup (v : Place K F) (n : ℕ) :
    Subgroup v.toValuationSubringˣ :=
  (unitReduction ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)).ker

/-- The kernel definition of local congruence agrees with ideal-power membership. -/
theorem mem_congruenceUnitSubgroup (v : Place K F) (n : ℕ)
    (u : v.toValuationSubringˣ) :
    u ∈ v.congruenceUnitSubgroup n ↔
      (u : v.toValuationSubring) - 1 ∈
        (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n := by
  change unitReduction _ u = 1 ↔ _
  rw [← Units.val_inj]
  change Ideal.Quotient.mk _ (u : v.toValuationSubring) = 1 ↔ _
  rw [← (Ideal.Quotient.mk _).map_one]
  exact Ideal.Quotient.eq

/-- Rational-function congruence is precisely a representative from the local
congruence subgroup. -/
theorem congruentOne_iff_exists_congruenceUnit (v : Place K F) (n : ℕ) (f : F) :
    v.CongruentOne n f ↔
      ∃ u : v.toValuationSubringˣ,
        ((u : v.toValuationSubring) : F) = f ∧ u ∈ v.congruenceUnitSubgroup n := by
  simp only [CongruentOne, mem_congruenceUnitSubgroup]

/-- The uniformizer power ideal equals the relevant maximal-ideal power. -/
theorem uniformizerPowerIdeal_eq_maximalIdeal_pow (v : Place K F)
    {π : v.toValuationSubring} (hπ : Irreducible π) (n : ℕ) :
    uniformizerPowerIdeal π n =
      (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rfl

/-- The existing higher-unit subgroup computes the canonical congruence subgroup. -/
theorem congruenceUnitSubgroup_eq_higherUnitSubgroup (v : Place K F)
    {π : v.toValuationSubring} (hπ : Irreducible π) (n : ℕ) :
    v.congruenceUnitSubgroup n = higherUnitSubgroup π n := by
  ext u
  rw [mem_congruenceUnitSubgroup,
    mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal,
    v.uniformizerPowerIdeal_eq_maximalIdeal_pow hπ n]

/-- Replacing a uniformizer preserves the entire higher-unit subgroup,
including the multiplicity. -/
theorem higherUnitSubgroup_uniformizer_independent (v : Place K F)
    {π ρ : v.toValuationSubring} (hπ : Irreducible π) (hρ : Irreducible ρ)
    (n : ℕ) : higherUnitSubgroup π n = higherUnitSubgroup ρ n := by
  rw [← v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ n,
    ← v.congruenceUnitSubgroup_eq_higherUnitSubgroup hρ n]

/-- The principal-unit filtration reverses the order on multiplicities. -/
theorem congruenceUnitSubgroup_antitone (v : Place K F) :
    Antitone v.congruenceUnitSubgroup := by
  intro m n hmn u hu
  rw [mem_congruenceUnitSubgroup] at hu ⊢
  exact Ideal.pow_le_pow_right hmn hu

/-- Reduction to a positive truncation of the valuation ring is a local map. -/
theorem unitReduction_isLocalHom (v : Place K F) {n : ℕ} (hn : n ≠ 0) :
    IsLocalHom
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)) :=
  isLocalHom_of_le_jacobson_bot _
    ((Ideal.pow_le_self hn).trans
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal v.toValuationSubring)))

/-- Every unit of a positive truncated local ring lifts to a local unit. -/
theorem unitReduction_surjective (v : Place K F) {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective
      (unitReduction ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)) := by
  let : IsLocalHom
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)) :=
    v.unitReduction_isLocalHom hn
  exact unitReduction_surjective_of_isLocalHom _

/-- The local-unit quotient is canonically the units of the truncated local ring. -/
def localUnitQuotientEquiv (v : Place K F) {n : ℕ} (hn : n ≠ 0) :
    v.toValuationSubringˣ ⧸ v.congruenceUnitSubgroup n ≃*
      (v.toValuationSubring ⧸
        (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective _ (v.unitReduction_surjective hn)

/-- The quotient equivalence sends a unit class to its actual reduction. -/
@[simp]
theorem localUnitQuotientEquiv_mk (v : Place K F) {n : ℕ} (hn : n ≠ 0)
    (u : v.toValuationSubringˣ) :
    v.localUnitQuotientEquiv hn (QuotientGroup.mk u) =
      unitReduction ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n) u :=
  rfl

end AlgebraicCurve.Place
