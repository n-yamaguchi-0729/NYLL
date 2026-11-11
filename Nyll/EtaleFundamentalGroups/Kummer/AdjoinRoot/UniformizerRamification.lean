/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
public import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic
public import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical

/-!
# The ramification index of a uniformizer root

For a DVR `R`, a uniformizer `π`, and a positive integer `n`, the actual
root algebra `R[X] / (X ^ n - π)` is a DVR whose ramification index over
`R` is exactly `n`. The proof identifies the extended maximal ideal with
the `n`-th power of the root ideal and excludes the next power.

The conclusion uses the length-based `Ideal.ramificationIdx`, through its
comparison with the ideal-power definition. No henselianity, separability,
or previously supplied ramification comparison is required.

This is the index calculation in Stacks Project, Lemma 15.116.2, used by
the standard tame cover of Example 58.31.4:
https://stacks.math.columbia.edu/tag/0EXT
https://stacks.math.columbia.edu/tag/0EYF
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The positive root of a uniformizer has exactly the prescribed
ramification index, measured by the length of the closed fibre. Both the
domain and DVR structures are constructed from the original data. -/
theorem ramificationIdx_adjoinRoot_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} (hn : 0 < n) (π : R) (hπ : Prime π) :
    let B := AdjoinRoot (X ^ n - C π)
    let : IsDomain B := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : IsDiscreteValuationRing B :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    (IsLocalRing.maximalIdeal B).ramificationIdx R = n := by
  intro B hdomain hdvr
  have : Module.FaithfullyFlat R B :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
  let x : B := AdjoinRoot.root (X ^ n - C π)
  have hx : Prime x := prime_adjoinRoot_root_of_prime hn hπ
  have hmax : IsLocalRing.maximalIdeal B = Ideal.span ({x} : Set B) :=
    hx.irreducible.maximalIdeal_eq
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R B) =
      IsLocalRing.maximalIdeal B ^ n := by
    rw [hπ.irreducible.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, hmax, Ideal.span_singleton_pow,
      AdjoinRoot.algebraMap_eq, ← adjoinRoot_root_pow]
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal B)
    (IsDiscreteValuationRing.not_a_field R)]
  apply Ideal.ramificationIdx'_spec hmap.le
  simp only [hmap, hmax, Ideal.span_singleton_pow,
    Ideal.span_singleton_le_span_singleton]
  intro hdiv
  exact (Nat.not_succ_le_self n)
    ((pow_dvd_pow_iff hx.ne_zero hx.not_isUnit).mp hdiv)

end EtaleFundamentalGroups.Kummer
