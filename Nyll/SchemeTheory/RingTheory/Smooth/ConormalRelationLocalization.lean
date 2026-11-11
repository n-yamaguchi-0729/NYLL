/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Clearing actual conormal generators near a prime

Nakayama removes the square of the relation ideal at the given prime.
Finite generation then supplies one actual denominator, outside that
prime, which makes every original relation belong to the selected ideal.
The base ring need not be Noetherian.
-/

@[expose] public section

noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- A localized inclusion of a finitely generated ideal has one denominator
which works for every original element. -/
theorem exists_notMem_mul_mem_of_map_le
    (I J p : Ideal R) (hI : I.FG) [p.IsPrime]
    (hle : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ r : R, r ∉ p ∧ ∀ x ∈ I, r * x ∈ J := by
  classical
  let S := Localization.AtPrime p
  obtain ⟨t, ht⟩ := hI
  have hex (i : ↥t) : ∃ s : p.primeCompl, (s : R) * (i : R) ∈ J := by
    have hi : algebraMap R S (i : R) ∈ J.map (algebraMap R S) :=
      hle (Ideal.mem_map_of_mem (algebraMap R S)
        (ht ▸ Submodule.subset_span i.property))
    obtain ⟨s, hs, hsi⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S J i).mp hi
    exact ⟨⟨s, hs⟩, hsi⟩
  choose s hs using hex
  let r : p.primeCompl := ∏ i : ↥t, s i
  refine ⟨r, r.property, ?_⟩
  have hspan : I ≤ Submodule.comap (LinearMap.mulLeft R (r : R)) (J : Submodule R R) := by
    rw [← ht]
    apply Submodule.span_le.mpr
    intro x hx
    let i : ↥t := ⟨x, hx⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ i)
    change (r : R) * x ∈ J
    have hr : r = s i * c := hc
    rw [hr]
    change ((s i : R) * (c : R)) * x ∈ J
    have heq : ((s i : R) * (c : R)) * x = (c : R) * ((s i : R) * (i : R)) := by
      change ((s i : R) * (c : R)) * x = (c : R) * ((s i : R) * x)
      ring
    rw [heq]
    exact J.mul_mem_left _ (hs i)
  intro x hx
  exact hspan hx

/-- Generators of the conormal module at a prime generate the original
relation ideal after one actual localization outside that prime. -/
theorem exists_notMem_mul_mem_of_conormal_generators
    (I J p : Ideal R) (hI : I.FG) [p.IsPrime] (hIp : I ≤ p)
    (q : R) (hq : q ∉ p) (hrel : ∀ x ∈ I, q * x ∈ J ⊔ I ^ 2) :
    ∃ r : R, r ∉ p ∧ ∀ x ∈ I, r * x ∈ J := by
  let S := Localization.AtPrime p
  let f : R →+* S := algebraMap R S
  let K := I.map f
  let L := J.map f
  have hunit : IsUnit (f q) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S p q).mpr hq
  have hKmax : K ≤ IsLocalRing.maximalIdeal S := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p x).mpr (hIp hx)
  have hKrel : K ≤ L ⊔ K ^ 2 := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change f x ∈ L ⊔ K ^ 2
    apply (Ideal.unit_mul_mem_iff_mem _ hunit).mp
    have hm := Ideal.mem_map_of_mem f (hrel x hx)
    rw [Ideal.map_sup, Ideal.map_pow, map_mul] at hm
    exact hm
  have hJac : K ≤ (⊥ : Ideal S).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact hKmax
  have hKle : K ≤ L := Submodule.le_of_le_smul_of_le_jacobson_bot
    (hI.map f) hJac (by simpa only [Ideal.smul_eq_mul, pow_two] using hKrel)
  exact exists_notMem_mul_mem_of_map_le I J p hI hKle

end Ideal
