/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_coboundary_at_infinity_of_smallExtension_of_split.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Lagrange
import Nyll.AlgebraicCurves.Geometry.LocalCoboundarySmallExtension

/-!
# Exists coboundary at infinity of small Extension of split
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Proofs.Exists_coboundary_at_infinity_of_smallExtension_of_split

open Polynomial

universe u v w w'

noncomputable section

namespace InfCobSol

open _root_.AlgebraicCurves.Geometry.Proofs
open Exists_local_coboundary_of_smallExtension_of_monogenic_fibre
open LocCobSol
open scoped LocCobSol LocCobSol.TAlg


section Twist

variable {S : Type*} [CommRing S] {N : ℕ} (d : Fin (N + 1) → ℕ)

theorem reflect_reflect (M : ℕ) (f : S[X]) : reflect M (reflect M f) = f := by
  ext i; rw [coeff_reflect, coeff_reflect, revAt_invol]

theorem reflect_sum {ι : Type*} (s : Finset ι) (f : ι → S[X]) (M : ℕ) :
    reflect M (∑ i ∈ s, f i) = ∑ i ∈ s, reflect M (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, reflect_add, ih]

/-- The degree-weighted reflection of the polynomial coefficients of the cochain. -/
def tw (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) :
    Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X] :=
  fun i j k => reflect (D + d i + d j - d k) (Φ i j k)

theorem tw_apply (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j k : Fin (N + 1))
  :
    tw d D Φ i j k = reflect (D + d i + d j - d k) (Φ i j k) := rfl

variable (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)

include hd0 hd in
theorem d_le_two (m : Fin (N + 1)) : d m ≤ 2 := by
  by_cases hm : m = 0
  · rw [hm, hd0]; exact Nat.zero_le _
  · rcases hd m hm with h | h <;> omega
include hd in
theorem one_le_d (m : Fin (N + 1)) (hm : m ≠ 0) : 1 ≤ d m := by
  rcases hd m hm with h | h <;> omega

theorem reflect_term (DΦ DΨ : ℕ)
    (Φ Ψ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (HΦ : ∀ i j k, (Φ i j k).natDegree ≤ DΦ + d i + d j - d k)
    (VΦ : ∀ i j k, d i + d j < d k → Φ i j k = 0)
    (HΨ : ∀ i j k, (Ψ i j k).natDegree ≤ DΨ + d i + d j - d k)
    (VΨ : ∀ i j k, d i + d j < d k → Ψ i j k = 0)
    (a b k c t : Fin (N + 1)) :
    reflect (DΦ + DΨ + (d a + d b + d c - d t)) (Φ a b k * Ψ k c t) =
      tw d DΦ Φ a b k * tw d DΨ Ψ k c t := by
  by_cases h1 : d a + d b < d k
  · rw [VΦ a b k h1, zero_mul, reflect_zero, tw_apply, VΦ a b k h1, reflect_zero, zero_mul]
  by_cases h2 : d k + d c < d t
  · rw [VΨ k c t h2, mul_zero, reflect_zero, tw_apply, tw_apply, VΨ k c t h2, reflect_zero,
      mul_zero]
  have hsum : DΦ + DΨ + (d a + d b + d c - d t) =
      (DΦ + d a + d b - d k) + (DΨ + d k + d c - d t) := by omega
  rw [hsum, reflect_mul _ _ (HΦ a b k) (HΨ k c t), tw_apply, tw_apply]

theorem reflect_P1 (DΦ DΨ : ℕ)
    (Φ Ψ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (HΦ : ∀ i j k, (Φ i j k).natDegree ≤ DΦ + d i + d j - d k)
    (VΦ : ∀ i j k, d i + d j < d k → Φ i j k = 0)
    (HΨ : ∀ i j k, (Ψ i j k).natDegree ≤ DΨ + d i + d j - d k)
    (VΨ : ∀ i j k, d i + d j < d k → Ψ i j k = 0)
    (i j l m : Fin (N + 1)) :
    reflect (DΦ + DΨ + (d i + d j + d l - d m)) (∑ k, Φ i j k * Ψ k l m) =
      ∑ k, tw d DΦ Φ i j k * tw d DΨ Ψ k l m := by
  rw [reflect_sum]
  exact Finset.sum_congr rfl fun k _ => reflect_term d DΦ DΨ Φ Ψ HΦ VΦ HΨ VΨ i j k l m

theorem reflect_P2 (DΦ DΨ : ℕ)
    (Φ Ψ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (HΦ : ∀ i j k, (Φ i j k).natDegree ≤ DΦ + d i + d j - d k)
    (VΦ : ∀ i j k, d i + d j < d k → Φ i j k = 0)
    (HΨ : ∀ i j k, (Ψ i j k).natDegree ≤ DΨ + d i + d j - d k)
    (VΨ : ∀ i j k, d i + d j < d k → Ψ i j k = 0)
    (Ψc : ∀ i j k, Ψ i j k = Ψ j i k)
    (i j l m : Fin (N + 1)) :
    reflect (DΦ + DΨ + (d i + d j + d l - d m)) (∑ k, Φ j l k * Ψ i k m) =
      ∑ k, tw d DΦ Φ j l k * tw d DΨ Ψ i k m := by
  rw [reflect_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hN : d i + d j + d l - d m = d j + d l + d i - d m := by omega
  rw [Ψc i k m, hN, reflect_term d DΦ DΨ Φ Ψ HΦ VΦ HΨ VΨ j l k i m, tw_apply, tw_apply,
    tw_apply, Ψc k i m, Nat.add_right_comm DΨ (d k) (d i)]

/-- The Hochschild coboundary of the polynomial-valued bilinear cochain in coordinates. -/
def D2 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j l m : Fin (N + 1)) : S[X] :=
  (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) + (∑ k, γ j l k * φ i k m) -
    (∑ k, φ i j k * γ k l m)

private def _root_.InfCobSol.assoc (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j l m :
  Fin (N + 1)) : S[X] :=
  (∑ k, γ i j k * γ k l m) - ∑ k, γ j l k * γ i k m

open _root_.InfCobSol
omit hd0 hd in
theorem reflect_assoc (Γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (H : ∀ i j k, (Γ i j k).natDegree ≤ 0 + d i + d j - d k)
    (V : ∀ i j k, d i + d j < d k → Γ i j k = 0) (Γc : ∀ i j k, Γ i j k = Γ j i k)
    (i j l m : Fin (N + 1)) :
    reflect (d i + d j + d l - d m) (assoc Γ i j l m) = assoc (tw d 0 Γ) i j l m := by
  have e : d i + d j + d l - d m = 0 + 0 + (d i + d j + d l - d m) := by ring
  rw [assoc, assoc, reflect_sub, e, reflect_P1 d 0 0 Γ Γ H V H V,
    reflect_P2 d 0 0 Γ Γ H V H V Γc]
omit hd0 hd in
theorem reflect_D2 (Dφ : ℕ) (Γ φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (H : ∀ i j k, (Γ i j k).natDegree ≤ 0 + d i + d j - d k)
    (V : ∀ i j k, d i + d j < d k → Γ i j k = 0) (Γc : ∀ i j k, Γ i j k = Γ j i k)
    (Hφ : ∀ i j k, (φ i j k).natDegree ≤ Dφ + d i + d j - d k)
    (Vφ : ∀ i j k, d i + d j < d k → φ i j k = 0) (φc : ∀ i j k, φ i j k = φ j i k)
    (i j l m : Fin (N + 1)) :
    reflect (Dφ + (d i + d j + d l - d m)) (D2 Γ φ i j l m) = D2 (tw d 0 Γ) (tw d Dφ φ) i j l m :=
      by
  have e1 : Dφ + (d i + d j + d l - d m) = Dφ + 0 + (d i + d j + d l - d m) := by ring
  have e2 : Dφ + (d i + d j + d l - d m) = 0 + Dφ + (d i + d j + d l - d m) := by ring
  have t1 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, φ j l k * Γ i k m) =
      ∑ k, tw d Dφ φ j l k * tw d 0 Γ i k m := by
    rw [e1]; exact reflect_P2 d Dφ 0 φ Γ Hφ Vφ H V Γc i j l m
  have t2 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, Γ i j k * φ k l m) =
      ∑ k, tw d 0 Γ i j k * tw d Dφ φ k l m := by
    rw [e2]; exact reflect_P1 d 0 Dφ Γ φ H V Hφ Vφ i j l m
  have t3 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, Γ j l k * φ i k m) =
      ∑ k, tw d 0 Γ j l k * tw d Dφ φ i k m := by
    rw [e2]; exact reflect_P2 d 0 Dφ Γ φ H V Hφ Vφ φc i j l m
  have t4 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, φ i j k * Γ k l m) =
      ∑ k, tw d Dφ φ i j k * tw d 0 Γ k l m := by
    rw [e1]; exact reflect_P1 d Dφ 0 φ Γ Hφ Vφ H V i j l m
  rw [D2, D2, reflect_sub, reflect_add, reflect_sub, t1, t2, t3, t4]

theorem tw_map {R₂ : Type*} [CommRing R₂] (f : S →+* R₂) (D : ℕ)
    (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j k : Fin (N + 1)) :
    (tw d D Φ i j k).map f = tw d D (fun i j k => (Φ i j k).map f) i j k := by
  rw [tw_apply, tw_apply, reflect_map]

theorem tw_tw (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j k : Fin (N + 1)) :
    tw d 0 (tw d 0 Φ) i j k = Φ i j k := by
  rw [tw_apply, tw_apply, reflect_reflect]

theorem natDegree_tw_le (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (H : ∀ i j k, (Φ i j k).natDegree ≤ D + d i + d j - d k) (i j k : Fin (N + 1)) :
    (tw d D Φ i j k).natDegree ≤ D + d i + d j - d k := by
  rw [tw_apply]
  exact natDegree_reflect_le.trans (max_le le_rfl (H i j k))

theorem tw_unit (hd0 : d 0 = 0) (_D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h : ∀ j k, Φ 0 j k = if j = k then 1 else 0) (j k : Fin (N + 1)) :
    tw d 0 Φ 0 j k = if j = k then 1 else 0 := by
  rw [tw_apply, h, hd0]
  split_ifs with hjk
  · subst hjk; simp only [zero_add, Nat.sub_self, reflect_one, pow_zero]
  · exact reflect_zero

theorem tw_comm (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h : ∀ i j k, Φ i j k = Φ j i k) (i j k : Fin (N + 1)) : tw d D Φ i j k = tw d D Φ j i k := by
  rw [tw_apply, tw_apply, h, Nat.add_right_comm]

theorem tw_zero_row (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h : ∀ j k, Φ 0 j k = 0) (j k : Fin (N + 1)) : tw d D Φ 0 j k = 0 := by
  rw [tw_apply, h, reflect_zero]

end Twist

section HV

variable {S : Type*} [CommRing S] {N : ℕ} (d : Fin (N + 1) → ℕ)
  (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)

theorem H_of_table (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h1 : ∀ j k, Φ 0 j k = if j = k then 1 else 0) (hc : ∀ i j k, Φ i j k = Φ j i k)
    (hdg : ∀ i j k, i ≠ 0 → j ≠ 0 → (Φ i j k).natDegree ≤ d i + d j - d k) (i j k : Fin (N + 1)) :
    (Φ i j k).natDegree ≤ 0 + d i + d j - d k := by
  rw [zero_add]
  by_cases hi : i = 0
  · subst hi; rw [h1]; split_ifs <;> simp only [natDegree_one, natDegree_zero, Nat.zero_le]
  by_cases hj : j = 0
  · subst hj; rw [hc, h1]; split_ifs <;> simp only [natDegree_one, natDegree_zero, Nat.zero_le]
  exact hdg i j k hi hj
include hd0 hd in
theorem V_of_table (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h1 : ∀ j k, Φ 0 j k = if j = k then 1 else 0) (hc : ∀ i j k, Φ i j k = Φ j i k)
    (i j k : Fin (N + 1)) (hlt : d i + d j < d k) : Φ i j k = 0 := by
  by_cases hi : i = 0
  · subst hi; rw [h1]; split_ifs with h
    · subst h; rw [hd0] at hlt; omega
    · rfl
  by_cases hj : j = 0
  · subst hj; rw [hc, h1]; split_ifs with h
    · subst h; rw [hd0] at hlt; omega
    · rfl
  have := d_le_two d hd0 hd k; have := one_le_d d hd i hi; have := one_le_d d hd j hj
  omega
include hd0 hd in
theorem V_of_cochain (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h1 : ∀ j k, Φ 0 j k = 0) (hc : ∀ i j k, Φ i j k = Φ j i k)
    (i j k : Fin (N + 1)) (hlt : d i + d j < d k) : Φ i j k = 0 := by
  by_cases hi : i = 0
  · subst hi; exact h1 j k
  by_cases hj : j = 0
  · subst hj; rw [hc]; exact h1 i k
  have := d_le_two d hd0 hd k; have := one_le_d d hd i hi; have := one_le_d d hd j hj
  omega

end HV

section Main

open _root_.InfCobSol

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {B : Type v} [CommRing B] [Algebra K[X] B]
theorem main
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (τ : Fin (n + 1) → Fin (n + 1) → K) (hτu : IsUnit (Matrix.det (Matrix.of τ)))
    (hτ0 : ∀ j, τ j 0 = 1)
    (hτm : ∀ j i i', i ≠ 0 → i' ≠ 0 →
      τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (hγ'd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (hacd : ∀ i j l m, (ac i j l m).natDegree ≤ d i + d j + d l - d m) :
    ∃ t : K[X], t ≠ 0 ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ t.natDegree + d i + d j - d k) ∧
      ∀ i j l m, D2 (fun i j k => b.repr (b i * b j) k) φ i j l m =
        t * (ac i j l m).map (ρ.comp π) := by
  classical
  set γB : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => b.repr (b i * b j) k
    with hγBdef
  have hγB1 : ∀ j k, γB 0 j k = if j = k then 1 else 0 := fun j k => by
    simp only [hγBdef, hb0, one_mul, b.repr_self, Finsupp.single_apply]
  have hγBc : ∀ i j k, γB i j k = γB j i k := fun i j k => by simp only [hγBdef, mul_comm]
  have hγBa : ∀ i j l m, ∑ k, γB i j k * γB k l m = ∑ k, γB j l k * γB i k m := repr_mul_assoc b
  have HγB := H_of_table d γB hγB1 hγBc hdeg
  have VγB := V_of_table d hd0 hd γB hγB1 hγBc
  have Hγ := H_of_table d γ hγ1 hγc hγd
  have Vγ := V_of_table d hd0 hd γ hγ1 hγc
  have Hγ' := H_of_table d γ' hγ'1 hγ'c hγ'd
  have Vγ' := V_of_table d hd0 hd γ' hγ'1 hγ'c
  let γBt := tw d 0 γB
  let γt := tw d 0 γ
  let γ't := tw d 0 γ'
  let act : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    reflect (d i + d j + d l - d m) (ac i j l m)
  have hγBt1 : ∀ j k, γBt 0 j k = if j = k then 1 else 0 := tw_unit d hd0 0 γB hγB1
  have hγBtc : ∀ i j k, γBt i j k = γBt j i k := tw_comm d 0 γB hγBc
  have hγBta : ∀ i j l m, ∑ k, γBt i j k * γBt k l m = ∑ k, γBt j l k * γBt i k m := by
    intro i j l m
    have := reflect_assoc d γB HγB VγB hγBc i j l m
    have h2 : assoc (tw d 0 γB) i j l m = 0 := by
      rw [← this, assoc, hγBa, sub_self, reflect_zero]
    rw [assoc, sub_eq_zero] at h2
    exact h2
  let Tt : Table K[X] n := ⟨γBt, hγBt1, hγBtc, hγBta⟩
  let Bt := TAlg Tt
  let bt : Module.Basis (Fin (n + 1)) K[X] Bt := TAlg.basis Tt
  have hbt0 : bt 0 = 1 := TAlg.basis_zero Tt
  have hbtrepr : ∀ i j k, bt.repr (bt i * bt j) k = γBt i j k := TAlg.repr_basis_mul_basis Tt
  have hγt1 : ∀ j k, γt 0 j k = if j = k then 1 else 0 := tw_unit d hd0 0 γ hγ1
  have hγtc : ∀ i j k, γt i j k = γt j i k := tw_comm d 0 γ hγc
  have hγta : ∀ i j l m, ∑ k, γt i j k * γt k l m = ∑ k, γt j l k * γt i k m := by
    intro i j l m
    have := reflect_assoc d γ Hγ Vγ hγc i j l m
    have h2 : assoc (tw d 0 γ) i j l m = 0 := by
      rw [← this, assoc, hγa, sub_self, reflect_zero]
    rw [assoc, sub_eq_zero] at h2
    exact h2
  have hγtB : ∀ i j k, (γt i j k).map ρ = bt.repr (bt i * bt j) k := by
    intro i j k
    rw [hbtrepr]
    change (tw d 0 γ i j k).map ρ = tw d 0 γB i j k
    rw [tw_map]
    congr 1
    funext i j k; exact hγB i j k
  have hγ't1 : ∀ j k, γ't 0 j k = if j = k then 1 else 0 := tw_unit d hd0 0 γ' hγ'1
  have hγ'tc : ∀ i j k, γ't i j k = γ't j i k := tw_comm d 0 γ' hγ'c
  have hγ'tπ : ∀ i j k, (γ't i j k).map π = γt i j k := by
    intro i j k
    change (tw d 0 γ' i j k).map π = tw d 0 γ i j k
    rw [tw_map]
    congr 1
    funext i j k; exact hγ'π i j k
  have hact : ∀ i j l m, (∑ k, γ't i j k * γ't k l m) - (∑ k, γ't j l k * γ't i k m) =
      C ε * act i j l m := by
    intro i j l m
    have := reflect_assoc d γ' Hγ' Vγ' hγ'c i j l m
    rw [assoc, assoc] at this
    change (∑ k, tw d 0 γ' i j k * tw d 0 γ' k l m) - (∑ k, tw d 0 γ' j l k * tw d 0 γ' i k m) = _
    rw [← this, hac, reflect_C_mul]
  set c : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K := fun x y z => (γB x y z).coeff (d x + d y -
    d z)
    with hcdef
  have hc0 : ∀ y z, c 0 y z = if y = z then 1 else 0 := by
    intro y z
    simp only [hcdef, hγB1, hd0, zero_add]
    split_ifs with h
    · subst h; rw [Nat.sub_self, coeff_one_zero]
    · exact coeff_zero _
  have hcc : ∀ x y z, c x y z = c y x z := fun x y z => by
    simp only [hcdef, hγBc x y z, Nat.add_comm (d x) (d y)]
  have hτm' : ∀ j i i', τ j i * τ j i' = ∑ k, c i i' k * τ j k := by
    intro j i i'
    by_cases hi : i = 0
    · subst hi
      rw [hτ0, one_mul]
      simp only [hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hi' : i' = 0
    · subst hi'
      rw [hτ0, mul_one]
      simp only [hcc i 0, hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]
    exact hτm j i i' hi hi'
  let TD : Table K n := Tt.map (Polynomial.constantCoeff : K[X] →+* K)
  have hTD : ∀ i j k, TD.γ i j k = c i j k := by
    intro i j k
    change ((tw d 0 γB i j k)).coeff 0 = (γB i j k).coeff (d i + d j - d k)
    rw [tw_apply, coeff_reflect, revAt_zero, zero_add]
  let D := TAlg TD
  let redD : Bt →+* D := TAlg.mapHom Tt TD Polynomial.constantCoeff (fun _ _ _ => rfl)
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of τ with hTdef
  let χf : D → (Fin (n + 1) → K) := fun x j => ∑ i, x.coord i * τ j i
  have hχmul : ∀ x y, χf (x * y) = χf x * χf y := by
    intro x y; funext j
    change ∑ m, (cst TD.γ x.coord y.coord m) * τ j m = (∑ i, x.coord i * τ j i) * ∑ k, y.coord k *
      τ j k
    simp only [cst_apply, hTD, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show x.coord i * τ j i * (y.coord k * τ j k) = x.coord i * y.coord k * (τ j i * τ j k)
      by ring,
      hτm' j i k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  let χ : D →+* (Fin (n + 1) → K) :=
    { toFun := χf
      map_one' := by
        funext j
        change ∑ i, (Pi.single 0 1 : Fin (n + 1) → K) i * τ j i = 1
        rw [Finset.sum_eq_single 0]
        · simp [hτ0]
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · intro h; exact absurd (Finset.mem_univ _) h
      map_mul' := hχmul
      map_zero' := by
        funext j
        change ∑ i, (0 : D).coord i * τ j i = 0
        simp [TAlg.coord_zero]
      map_add' := fun x y => by
        funext j
        change ∑ i, (x + y).coord i * τ j i = (∑ i, x.coord i * τ j i) + ∑ i, y.coord i * τ j i
        rw [TAlg.coord_add]
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib] }
  have hχ : ∀ x j, χ x j = ∑ i, x.coord i * τ j i := fun x j => rfl
  have hχT : ∀ x, χ x = T.mulVec x.coord := by
    intro x; funext j
    rw [hχ, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [hTdef, Matrix.of_apply, mul_comm]
  have hχinj : Function.Injective χ := by
    intro x y hxy
    ext1
    have h1 : T.mulVec x.coord = T.mulVec y.coord := by rw [← hχT, ← hχT, hxy]
    have h2 := congrArg (T⁻¹.mulVec) h1
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hτu,
      Matrix.one_mulVec, Matrix.one_mulVec] at h2
  let aK : Fin (n + 1) → K := fun i => Infinite.natEmbedding K i
  have haK : Function.Injective aK := fun i j h =>
    Fin.ext ((Infinite.natEmbedding K).injective h)
  let yv : Fin (n + 1) → K := T⁻¹.mulVec aK
  have hyv : T.mulVec yv = aK := by
    change T.mulVec (T⁻¹.mulVec aK) = aK
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hτu, Matrix.one_mulVec]
  let y : Bt := TAlg.mk fun i => C (yv i)
  have hredy : redD y = TAlg.mk yv := by
    ext1; funext i
    change Polynomial.constantCoeff (C (yv i)) = yv i
    rw [Polynomial.constantCoeff_apply, coeff_C_zero]
  have hχy : χ (redD y) = aK := by rw [hχT, hredy, ← hyv]
  have hscal : χ.comp (redD.comp ((algebraMap K[X] Bt).comp C)) =
      algebraMap K (Fin (n + 1) → K) := by
    refine RingHom.ext fun c0 => funext fun j => ?_
    change ∑ i, Polynomial.constantCoeff ((algebraMap K[X] Bt (C c0)).coord i) * τ j i = c0
    rw [TAlg.algebraMap_coord, Finset.sum_eq_single 0]
    · rw [Pi.single_eq_same, Polynomial.constantCoeff_apply, coeff_C_zero, hτ0, mul_one]
    · intro i _ hi; rw [Pi.single_eq_of_ne hi, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPmax : (Ideal.span {(X : K[X])}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hmonoBt : ∃ y0 : Bt, ∀ z : Bt, ∃ q : Polynomial K[X],
      z - aeval y0 q ∈ (Ideal.span {(X : K[X])}) • (⊤ : Submodule K[X] Bt) := by
    refine ⟨y, fun z => ?_⟩
    let r : Fin (n + 1) → K := χ (redD z)
    let q₀ : K[X] := Lagrange.interpolate Finset.univ aK r
    refine ⟨q₀.map C, ?_⟩
    have hq₀ : ∀ j, q₀.eval (aK j) = r j := fun j =>
      Lagrange.eval_interpolate_at_node r haK.injOn (Finset.mem_univ j)
    have hev : ∀ (x : Fin (n + 1) → K) (j : Fin (n + 1)),
        (eval₂ (algebraMap K (Fin (n + 1) → K)) x q₀) j = q₀.eval (x j) := by
      intro x j
      have := hom_eval₂ q₀ (algebraMap K (Fin (n + 1) → K)) (Pi.evalRingHom (fun _ => K) j) x
      rw [Pi.evalRingHom_apply] at this
      rw [this]
      rfl
    have h1 : χ (redD (aeval y (q₀.map C))) = χ (redD z) := by
      rw [aeval_def, eval₂_map, hom_eval₂, hom_eval₂, hscal, hχy]
      funext j
      rw [hev, hq₀]
    have h2 : redD (z - aeval y (q₀.map C)) = 0 :=
      hχinj (by rw [map_sub, map_sub, h1, sub_self, map_zero])
    have h3 : ∀ k, (z - aeval y (q₀.map C)).coord k ∈ Ideal.span {(X : K[X])} := by
      intro k
      rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
      have := congrArg (fun x : D => x.coord k) h2
      change ((z - aeval y (q₀.map C)).coord k).coeff 0 = 0 at this
      exact this
    rw [TAlg.eq_sum_coord_smul_basis Tt (z - aeval y (q₀.map C))]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (h3 k) Submodule.mem_top
  obtain ⟨s, hs, φt, hφt1, hφtc, hφtD⟩ :=
    AlgebraicCurve.exists_local_coboundary_of_smallExtension_of_monogenic_fibre K n Bt bt hbt0
      A' A π hπ ε hker ρ hρ hann γt hγt1 hγtc hγta hγtB γ't hγ't1 hγ'tc hγ'tπ act hact
      (Ideal.span {(X : K[X])}) hPmax hmonoBt
  have hφtD' : ∀ i j l m, D2 γBt φt i j l m = s * (act i j l m).map (ρ.comp π) := by
    intro i j l m
    rw [← hφtD i j l m, D2]
    simp only [hbtrepr]
  let Dφ : ℕ := (Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) =>
    (φt p.1 p.2.1 p.2.2).natDegree) ⊔ s.natDegree
  have hDφ : ∀ i j k, (φt i j k).natDegree ≤ Dφ := fun i j k =>
    le_sup_of_le_left (Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) =>
      (φt p.1 p.2.1 p.2.2).natDegree) (Finset.mem_univ (i, j, k)))
  have hDs : s.natDegree ≤ Dφ := le_sup_right
  have Vφt := V_of_cochain d hd0 hd φt hφt1 hφtc
  have Hφt : ∀ i j k, (φt i j k).natDegree ≤ Dφ + d i + d j - d k := by
    intro i j k
    by_cases h : d i + d j < d k
    · rw [Vφt i j k h, natDegree_zero]; exact Nat.zero_le _
    · exact (hDφ i j k).trans (by omega)
  have HγBt : ∀ i j k, (γBt i j k).natDegree ≤ 0 + d i + d j - d k := natDegree_tw_le d 0 γB HγB
  have VγBt : ∀ i j k, d i + d j < d k → γBt i j k = 0 := fun i j k h => by
    change tw d 0 γB i j k = 0
    rw [tw_apply, VγB i j k h, reflect_zero]
  let φ := tw d Dφ φt
  let t := reflect Dφ s
  have hs0 : s.coeff 0 ≠ 0 := fun h =>
    hs (Ideal.mem_span_singleton.2 (Polynomial.X_dvd_iff.2 h))
  have htcoeff : t.coeff Dφ = s.coeff 0 := by
    change (reflect Dφ s).coeff Dφ = _
    rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self]
  have ht0 : t ≠ 0 := fun h => hs0 (by rw [← htcoeff, h, coeff_zero])
  have htdeg : t.natDegree = Dφ :=
    le_antisymm (natDegree_reflect_le.trans (max_le le_rfl hDs))
      (le_natDegree_of_ne_zero (by rw [htcoeff]; exact hs0))
  have hφD2 : ∀ i j l m, D2 γB φ i j l m = t * (ac i j l m).map (ρ.comp π) := by
    intro i j l m
    have h := congrArg (reflect (Dφ + (d i + d j + d l - d m))) (hφtD' i j l m)
    rw [reflect_D2 d Dφ γBt φt HγBt VγBt hγBtc Hφt Vφt hφtc] at h
    have htw : tw d 0 γBt = γB := by
      funext i j k; exact tw_tw d γB i j k
    rw [htw] at h
    change D2 γB (tw d Dφ φt) i j l m = reflect Dφ s * (ac i j l m).map (ρ.comp π)
    rw [h]
    change reflect (Dφ + (d i + d j + d l - d m))
      (s * (reflect (d i + d j + d l - d m) (ac i j l m)).map (ρ.comp π)) = _
    have hdeg2 : ((reflect (d i + d j + d l - d m) (ac i j l m)).map (ρ.comp π)).natDegree ≤
        d i + d j + d l - d m := by
      rw [← reflect_map]
      exact natDegree_reflect_le.trans (max_le le_rfl (natDegree_map_le.trans (hacd i j l m)))
    rw [reflect_mul _ _ hDs hdeg2, ← reflect_map, reflect_reflect]
  refine ⟨t, ht0, φ, fun j k => tw_zero_row d Dφ φt hφt1 j k, fun i j k => tw_comm d Dφ φt hφtc i j
    k,
    fun i j k hi hj => ?_, hφD2⟩
  rw [htdeg]
  exact natDegree_tw_le d Dφ φt Hφt i j k

end Main

end InfCobSol

end

theorem _root_.AlgebraicCurve.exists_coboundary_at_infinity_of_smallExtension_of_split
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (hγ'd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (hacd : ∀ i j l m, (ac i j l m).natDegree ≤ d i + d j + d l - d m) :
    ∃ t : K[X], t ≠ 0 ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ t.natDegree + d i + d j - d k) ∧
      ∀ i j l m, (∑ k, φ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * φ k l m) +
          (∑ k, b.repr (b j * b l) k * φ i k m) - (∑ k, φ i j k * b.repr (b k * b l) m) =
        t * (ac i j l m).map (ρ.comp π) := by
  obtain ⟨τ, hτu, hτ0, hτm⟩ := hinf
  exact InfCobSol.main b d hb0 hd0 hd hdeg τ hτu hτ0 hτm A' A π hπ ε hker ρ hρ hann γ hγ1 hγc hγa
    hγd
    hγB γ' hγ'1 hγ'c hγ'π hγ'd ac hac hacd
end AlgebraicCurves.Geometry.Proofs.Exists_coboundary_at_infinity_of_smallExtension_of_split
end ProofImplementation
