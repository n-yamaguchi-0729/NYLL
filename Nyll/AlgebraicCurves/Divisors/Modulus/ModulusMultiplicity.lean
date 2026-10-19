/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusLocalUnits

/-!
# Strict dependence on the modulus multiplicity

The unit `1 + π^n` is congruent to one modulo the `n`-th maximal-ideal power
and fails the next congruence. This gives an explicit mathematical check that
a doubled point has not been replaced by its reduced support.
-/

noncomputable section

namespace AlgebraicCurve

open LubinTate.Valuations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Every positive step of the local congruence filtration is strictly stronger
than its predecessor. The witness is `1 + π^n` for any uniformizer `π`. -/
theorem Place.exists_congruentOne_not_succ (v : Place K F) (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : F, v.CongruentOne n f ∧ ¬ v.CongruentOne (n + 1) f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  let u : higherUnitSubgroup π n := higherUnitOneAdd hπ n hn 1
  have hu : (u : v.toValuationSubringˣ) ∈ v.congruenceUnitSubgroup n := by
    rw [v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ]
    exact u.property
  refine ⟨(((u : v.toValuationSubringˣ) : v.toValuationSubring) : F),
    ⟨u, rfl, (v.mem_congruenceUnitSubgroup n u).mp hu⟩, ?_⟩
  rintro ⟨w, hw, hmem⟩
  have hwu : w = (u : v.toValuationSubringˣ) := Units.ext (Subtype.ext hw)
  rw [hwu] at hmem
  have hnext : (u : v.toValuationSubringˣ) ∈ higherUnitSubgroup π (n + 1) := by
    rw [← v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ,
      v.mem_congruenceUnitSubgroup]
    exact hmem
  have hker : u ∈ (higherUnitCoeffModHom hπ.ne_zero n hn).ker := by
    rw [higherUnitCoeffModHom_ker]
    exact hnext
  have hzero : Ideal.Quotient.mk (Ideal.span ({π} : Set v.toValuationSubring))
      (1 : v.toValuationSubring) = 0 := by
    have heq := MonoidHom.mem_ker.mp hker
    change higherUnitCoeffModHom hπ.ne_zero n hn (higherUnitOneAdd hπ n hn 1) = 1 at heq
    rw [higherUnitCoeffModHom_oneAdd] at heq
    exact congrArg Multiplicative.toAdd heq
  have hdiv : π ∣ (1 : v.toValuationSubring) :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  exact hπ.not_isUnit (isUnit_of_dvd_one hdiv)

/-- A simple point and the doubled point impose genuinely different global
modulus conditions. -/
theorem Modulus.exists_congruentOne_single_not_double (v : Place K F) :
    ∃ f : F,
      Modulus.CongruentOne (Finsupp.single v 1 : Modulus K F) f ∧
        ¬ Modulus.CongruentOne (Finsupp.single v 2 : Modulus K F) f := by
  obtain ⟨f, hf, hf'⟩ := v.exists_congruentOne_not_succ 1 (le_refl 1)
  refine ⟨f, (Modulus.congruentOne_single v 1 f).mpr ⟨hf.ne_zero, fun _ => hf⟩, ?_⟩
  intro h
  exact hf' (((Modulus.congruentOne_single v 2 f).mp h).2 (by decide))

end AlgebraicCurve
