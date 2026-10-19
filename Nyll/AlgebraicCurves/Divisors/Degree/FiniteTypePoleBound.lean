/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite pole bounds for actual affine coordinate maps

A map from a finitely generated coordinate algebra to the function field has
finitely many generators with a common finite pole bound. Away from its
support, the entire coordinate map lands in the actual valuation ring.
This is a pole-bound supplier for rational maps; no reciprocity or modulus
condition for the target group is asserted here.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [HasPrincipalDivisors K F]

/-- The negative orders of a rational function define an actual finite
nonnegative divisor, including for the zero function. -/
theorem exists_poleOrderDivisor (f : F) :
    ∃ D : Modulus K F, ∀ v : Place K F, D v = (-v.ord f).toNat := by
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    intro v
    rw [hf, Place.ord_zero, neg_zero, Int.toNat_zero, Finsupp.zero_apply]
  · obtain ⟨E, hE, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    refine ⟨E.mapRange (fun n : ℤ => (-n).toNat) rfl, ?_⟩
    intro v
    rw [Finsupp.mapRange_apply, hE v]

/-- Finitely many rational coordinate functions have a common finite pole
bound, whose support is exactly their union of pole sets. -/
theorem exists_finset_pole_bound {ι : Type*} (S : Finset ι) (f : ι → F) :
    ∃ D : Modulus K F,
      (∀ v : Place K F, ∀ a ∈ S, -(D v : ℤ) ≤ v.ord (f a)) ∧
      (∀ v : Place K F, D v = 0 ↔ ∀ a ∈ S, 0 ≤ v.ord (f a)) := by
  classical
  choose E hE using fun a => exists_poleOrderDivisor (K := K) (f a)
  let D : Modulus K F := ∑ a ∈ S, E a
  have hD (v : Place K F) : D v = ∑ a ∈ S, (-v.ord (f a)).toNat := by
    simp only [D, Finsupp.finsetSum_apply, hE]
  have hle (v : Place K F) (a : ι) (ha : a ∈ S) :
      (-v.ord (f a)).toNat ≤ D v := by
    rw [hD]
    exact Finset.single_le_sum (fun b _ => Nat.zero_le ((-v.ord (f b)).toNat)) ha
  refine ⟨D, ?_, ?_⟩
  · intro v a ha
    have h := hle v a ha
    omega
  · intro v
    constructor
    · intro hv a ha
      have h := hle v a ha
      rw [hv] at h
      omega
    · intro hv
      rw [hD]
      apply Finset.sum_eq_zero
      intro a ha
      have h := hv a ha
      omega

/-- An actual coordinate-algebra map admits finitely many bounded generators,
and outside those poles every coordinate function is regular in the full
valuation ring. No choice of abstract target-point values is involved. -/
theorem exists_finiteType_pole_bound {A : Type*} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (φ : A →ₐ[K] F) :
    ∃ (S : Finset A) (D : Modulus K F),
      Algebra.adjoin K (S : Set A) = ⊤ ∧
      (∀ v : Place K F, ∀ a ∈ S, -(D v : ℤ) ≤ v.ord (φ a)) ∧
      (∀ v : Place K F, D v = 0 ↔ ∀ a : A, φ a ∈ v.toValuationSubring) := by
  classical
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := K) (A := A)
  obtain ⟨D, hbound, hzero⟩ := exists_finset_pole_bound (K := K) S φ
  refine ⟨S, D, hS, hbound, ?_⟩
  intro v
  constructor
  · intro hv a
    have hgen : ∀ b ∈ S, φ b ∈ v.toValuationSubring := by
      intro b hb
      by_cases hφb : φ b = 0
      · rw [hφb]
        exact v.toValuationSubring.zero_mem
      · exact v.mem_of_ord_nonneg hφb ((hzero v).mp hv b hb)
    have ha : a ∈ Algebra.adjoin K (S : Set A) := by
      rw [hS]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem b hb => exact hgen b hb
    | algebraMap r =>
      rw [φ.commutes]
      exact v.algebraMap_mem' r
    | add b c _ _ hb hc =>
      rw [map_add]
      exact add_mem hb hc
    | mul b c _ _ hb hc =>
      rw [map_mul]
      exact mul_mem hb hc
  · intro hv
    apply (hzero v).mpr
    intro a _
    exact v.ord_nonneg_of_mem (hv a)

/-- The actual generic affine map extends over every valuation ring outside
one finite divisor. The supplied homomorphisms retain the original map to
the function field, so applying `Spec` gives genuine local extensions. -/
theorem exists_finiteType_valuation_extensions {A : Type*} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (φ : A →ₐ[K] F) :
    ∃ D : Modulus K F, ∀ v : Place K F, D v = 0 →
      ∃ ψ : A →ₐ[K] v.toValuationSubring,
        (IsScalarTower.toAlgHom K v.toValuationSubring F).comp ψ = φ := by
  obtain ⟨_, D, _, _, hD⟩ := exists_finiteType_pole_bound φ
  refine ⟨D, ?_⟩
  intro v hv
  let ψ : A →ₐ[K] v.toValuationSubring :=
    { toRingHom := φ.toRingHom.codRestrict v.toValuationSubring.toSubring ((hD v).mp hv)
      commutes' := fun r => Subtype.ext (φ.commutes r) }
  exact ⟨ψ, AlgHom.ext (fun _ => rfl)⟩

end AlgebraicCurve
