/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Increasing the ideal order of a flat relation

A formal smooth lift of a relation algebra carries a relation with
coefficients in `K` into the extended ideal `K * I`, whenever the
quotient error ideal lies in `I` and `I` is nilpotent. Its composite to
the target is unchanged. Iterating this construction increases the
ideal order until nilpotence makes the relation zero.

This is the weighted-relation calculation in the nilpotent lifting
argument of Stacks Project, Lemmas 16.5.2 and 16.5.3:
https://stacks.math.columbia.edu/tag/07CL
https://stacks.math.columbia.edu/tag/07CM
-/

@[expose] public section

noncomputable section

namespace Algebra

/-- Lifting an actual quotient factorization increases the ideal order
of a weighted relation from `K` to `K * I`. -/
theorem exists_lift_relation_mem_mul_of_nilpotent
    {R B C D L : Type*}
    [CommRing R] [CommRing B] [CommRing C] [CommRing D] [CommRing L]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R L]
    [FormallySmooth R B]
    (I : Ideal R) (hI : IsNilpotent I) (K : Ideal R) (J : Ideal D)
    (hJI : J ≤ I.map (algebraMap R D))
    (γ : B →ₐ[R] C) (η : C →ₐ[R] D ⧸ J) (β : D ⧸ J →ₐ[R] L)
    {ι : Type*} [Fintype ι] {m : ℕ}
    (ε : ι → R) (hε : ∀ i, ε i ∈ K) (b : ι → B)
    (a : ι → Fin m → R) (ξ : Fin m → C)
    (hb : ∀ i, γ (b i) = ∑ j, a i j • ξ j)
    (ha : ∀ j, ∑ i, ε i * a i j = 0) :
    ∃ α : B →ₐ[R] D,
      α (∑ i, ε i • b i) ∈ (K * I).map (algebraMap R D) ∧
        (β.comp (Ideal.Quotient.mkₐ R J)).comp α = β.comp (η.comp γ) := by
  let ID := I.map (algebraMap R D)
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hI
    have hID : ID ^ n = ⊥ := by
      change I.map (algebraMap R D) ^ n = ⊥
      rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    have hJn : J ^ n = ⊥ := by
      apply le_bot_iff.mp
      exact (pow_le_pow_left' hJI n).trans hID.le
    exact ⟨n, hJn.trans Ideal.zero_eq_bot.symm⟩
  obtain ⟨α, hα⟩ := FormallySmooth.exists_lift J hJ (η.comp γ)
  choose ξ' hξ' using fun j => Ideal.Quotient.mk_surjective (η (ξ j))
  let q : D →ₐ[R] D ⧸ J := Ideal.Quotient.mkₐ R J
  have hξq (j : Fin m) : q (ξ' j) = η (ξ j) := hξ' j
  have hdiff (i : ι) : α (b i) - ∑ j, a i j • ξ' j ∈ ID := by
    apply hJI
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (α (b i) - ∑ j, a i j • ξ' j) = 0
    rw [map_sub, map_sum]
    simp only [map_smul, hξq]
    have hi := AlgHom.congr_fun hα (b i)
    change q (α (b i)) = η (γ (b i)) at hi
    rw [hi, hb, map_sum]
    simp only [map_smul, sub_self]
  have hweighted (i : ι) :
      ε i • (α (b i) - ∑ j, a i j • ξ' j) ∈
        (K * I).map (algebraMap R D) := by
    rw [Algebra.smul_def, Ideal.map_mul]
    exact Ideal.mul_mem_mul
      (Ideal.mem_map_of_mem (algebraMap R D) (hε i)) (hdiff i)
  have hzero : (∑ i, ε i • (∑ j, a i j • ξ' j)) = 0 :=
    Module.sum_smul_eq_zero_of_isTrivialRelation
      ⟨m, a, ξ', fun _ => rfl, ha⟩
  have heq : α (∑ i, ε i • b i) =
      ∑ i, ε i • (α (b i) - ∑ j, a i j • ξ' j) := by
    rw [map_sum]
    simp only [map_smul, smul_sub, Finset.sum_sub_distrib, hzero, sub_zero]
  refine ⟨α, ?_, ?_⟩
  · rw [heq]
    exact Submodule.sum_mem _ fun i _ => hweighted i
  · rw [AlgHom.comp_assoc, hα]

end Algebra
