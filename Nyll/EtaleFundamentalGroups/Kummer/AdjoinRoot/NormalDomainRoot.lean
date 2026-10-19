/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Obstructions.LocalDerivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Prime root polynomials over normal domains

A positive root polynomial of a prime element is irreducible over the
fraction field. Monic division reflects divisibility along the injective
coefficient map, so primality descends to the original polynomial ring.
Consequently the actual root chart is a domain in arbitrary dimension;
no unique factorization or DVR hypothesis is needed.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

/-- The positive root polynomial of a prime element of a normal domain
is itself prime. Monic division supplies descent from the fraction field. -/
theorem prime_X_pow_sub_C_of_prime_of_isIntegrallyClosed
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {n : ℕ} (hn : 0 < n) {p : R} (hp : Prime p) : Prime (X ^ n - C p) := by
  let K := FractionRing R
  let f : R[X] := X ^ n - C p
  have hfMonic : f.Monic := monic_X_pow_sub_C p hn.ne'
  have hfIrred : Irreducible f := irreducible_X_pow_sub_C_of_prime hp hn
  have hfPrimeMap : Prime (f.map (algebraMap R K)) := by
    have h : Irreducible (X ^ n - C (algebraMap R K p)) :=
      irreducible_X_pow_sub_C_fractionRing_of_prime hp hn
    simpa only [f, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C] using h.prime
  refine ⟨hfMonic.ne_zero, hfIrred.not_isUnit, ?_⟩
  intro a b hab
  have hmapped : f.map (algebraMap R K) ∣
      a.map (algebraMap R K) * b.map (algebraMap R K) := by
    rw [← Polynomial.map_mul]
    exact (Polynomial.map_dvd_map (algebraMap R K)
      (IsFractionRing.injective R K) hfMonic).mpr hab
  rcases hfPrimeMap.dvd_or_dvd hmapped with ha | hb
  · exact Or.inl ((Polynomial.map_dvd_map (algebraMap R K)
      (IsFractionRing.injective R K) hfMonic).mp ha)
  · exact Or.inr ((Polynomial.map_dvd_map (algebraMap R K)
      (IsFractionRing.injective R K) hfMonic).mp hb)

/-- A positive root of a prime element over a normal domain gives a
domain, with the literal polynomial quotient as its underlying ring. -/
theorem isDomain_adjoinRoot_X_pow_sub_C_of_isIntegrallyClosed
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {n : ℕ} (hn : 0 < n) {p : R} (hp : Prime p) :
    IsDomain (AdjoinRoot (X ^ n - C p)) :=
  AdjoinRoot.isDomain_of_prime (prime_X_pow_sub_C_of_prime_of_isIntegrallyClosed hn hp)

end EtaleFundamentalGroups.Kummer
