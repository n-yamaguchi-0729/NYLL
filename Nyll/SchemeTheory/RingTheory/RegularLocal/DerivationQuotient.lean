/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Derivation.IdealPowers
public import Nyll.SchemeTheory.RingTheory.RegularLocal.QuotientRegular
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular quotients detected by derivations

An invertible matrix of values of derivations on relations makes those
relations part of a regular system of parameters. We normalize the
derivations using the inverse matrix and then successively descend the
remaining derivations through each principal quotient.

The principal regular-quotient theorem, quotient derivation construction,
and quotient comparison are existing suppliers. The new connection is the
finite Jacobian criterion without a finite-type assumption on the ring;
in particular it can consume derivations on an adic completion.
-/

@[expose] public section

noncomputable section

open IsLocalRing

namespace Derivation

universe u v

variable {K : Type u} [CommRing K] {R : Type v} [CommRing R] [Algebra K R]

/-- A unit derivative detects a nonzero cotangent class. -/
theorem notMem_maximalIdeal_sq_of_isUnit [IsLocalRing R]
    (D : Derivation K R R) {x : R} (hD : IsUnit (D x)) :
    x ∉ maximalIdeal R ^ 2 := by
  intro hx
  apply (IsLocalRing.notMem_maximalIdeal.mpr hD)
  simpa only [pow_one] using D.map_mem_pow_succ (maximalIdeal R) 1 hx

/-- The principal Jacobian criterion, using the existing regular parameter
quotient theorem. -/
theorem isRegularLocalRing_quotient_singleton_of_isUnit [IsRegularLocalRing R]
    (D : Derivation K R R) {x : R} (hx : x ∈ maximalIdeal R)
    (hD : IsUnit (D x)) : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
  RegularQuotientEngine.isRegularLocalRing_quotient_span_singleton R hx
    (D.notMem_maximalIdeal_sq_of_isUnit hD)

private theorem preserves_span_singleton_of_eq_zero
    (D : Derivation K R R) (x : R) (hD : D x = 0) :
    ∀ y, Ideal.Quotient.mkₐ K (Ideal.span {x}) y = 0 →
      Ideal.Quotient.mkₐ K (Ideal.span {x}) (D y) = 0 := by
  intro y hy
  have hy' : y ∈ Ideal.span {x} := Ideal.Quotient.eq_zero_iff_mem.mp hy
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy'
  change Ideal.Quotient.mk (Ideal.span {x}) (D (a * x)) = 0
  rw [D.leibniz, smul_eq_mul, smul_eq_mul, hD, mul_zero, zero_add,
    map_mul, Ideal.Quotient.mk_singleton_self, zero_mul]

private def quotientOfKillsGenerator (D : Derivation K R R)
    (x : R) (hD : D x = 0) :
    Derivation K (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) :=
  Derivation.liftOfSurjective
    (f := Ideal.Quotient.mkₐ K (Ideal.span {x}))
    Ideal.Quotient.mk_surjective
    (D.preserves_span_singleton_of_eq_zero x hD)

private theorem quotientOfKillsGenerator_apply (D : Derivation K R R)
    (x : R) (hD : D x = 0) (y : R) :
    D.quotientOfKillsGenerator x hD (Ideal.Quotient.mk (Ideal.span {x}) y) =
      Ideal.Quotient.mk (Ideal.span {x}) (D y) := by
  exact Derivation.liftOfSurjective_apply
    (f := Ideal.Quotient.mkₐ K (Ideal.span {x}))
    Ideal.Quotient.mk_surjective
    (D.preserves_span_singleton_of_eq_zero x hD) y

/-- Relations with dual derivations give a regular quotient. The proof
descends the actual derivations after each relation is killed. -/
theorem isRegularLocalRing_quotient_of_dual :
    ∀ (n : ℕ) (R : Type v) [CommRing R] [Algebra K R] [IsRegularLocalRing R]
      (f : Fin n → R) (D : Fin n → Derivation K R R),
      (∀ i, f i ∈ maximalIdeal R) →
      (∀ i j, D i (f j) = if i = j then 1 else 0) →
      IsRegularLocalRing (R ⧸ Ideal.span (Set.range f)) := by
  intro n
  induction n with
  | zero =>
      intro R _ _ _ f D hf hD
      have hI : Ideal.span (Set.range f) = ⊥ := by
        rw [Set.range_eq_empty, Ideal.span_empty]
      exact IsRegularLocalRing.of_ringEquiv
        ((RingEquiv.quotientBot R).symm.trans (Ideal.quotEquivOfEq hI.symm))
  | succ n ih =>
      intro R _ _ _ f D hf hD
      let q := Ideal.Quotient.mk (Ideal.span {f 0})
      have hD₀ : IsUnit (D 0 (f 0)) := by
        rw [hD, ite_eq_left rfl]
        exact isUnit_one
      have : IsRegularLocalRing (R ⧸ Ideal.span {f 0}) :=
        (D 0).isRegularLocalRing_quotient_singleton_of_isUnit (hf 0) hD₀
      have hkill (i : Fin n) : D i.succ (f 0) = 0 := by
        rw [hD, ite_eq_right (Fin.succ_ne_zero i)]
      let D' : Fin n → Derivation K (R ⧸ Ideal.span {f 0}) (R ⧸ Ideal.span {f 0}) :=
        fun i => (D i.succ).quotientOfKillsGenerator (f 0) (hkill i)
      let f' : Fin n → R ⧸ Ideal.span {f 0} := fun i => q (f i.succ)
      have hf' (i : Fin n) : f' i ∈ maximalIdeal (R ⧸ Ideal.span {f 0}) := by
        rw [← IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective]
        exact Ideal.mem_map_of_mem q (hf i.succ)
      have hD' (i j : Fin n) : D' i (f' j) = if i = j then 1 else 0 := by
        change (D i.succ).quotientOfKillsGenerator (f 0) (hkill i)
          (Ideal.Quotient.mk (Ideal.span {f 0}) (f j.succ)) = _
        rw [quotientOfKillsGenerator_apply, hD]
        by_cases hij : i = j
        · subst j
          rw [ite_eq_left rfl, ite_eq_left rfl, map_one]
        · rw [ite_eq_right (fun h => hij (Fin.succ_inj.mp h)), ite_eq_right hij, map_zero]
      have : IsRegularLocalRing
          ((R ⧸ Ideal.span {f 0}) ⧸ Ideal.span (Set.range f')) :=
        ih (R ⧸ Ideal.span {f 0}) f' D' hf' hD'
      have hmap : (Ideal.span (Set.range (fun i : Fin n => f i.succ))).map q =
          Ideal.span (Set.range f') := by
        rw [Ideal.map_span, ← Set.range_comp']
      have hspan : Ideal.span (Set.range f) =
          Ideal.span {f 0} ⊔ Ideal.span (Set.range (fun i : Fin n => f i.succ)) := by
        rw [Fin.range_fin_succ, Ideal.span_insert]
        rfl
      exact IsRegularLocalRing.of_ringEquiv
        ((Ideal.quotEquivOfEq hmap.symm).trans
          ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {f 0})
            (Ideal.span (Set.range (fun i : Fin n => f i.succ)))).trans
              (Ideal.quotEquivOfEq hspan.symm)))

/-- An invertible Jacobian of finitely many derivations gives a regular
quotient, even when the ambient ring is not of finite type over `K`. -/
theorem isRegularLocalRing_quotient_of_isUnit_det [IsRegularLocalRing R]
    (n : ℕ) (f : Fin n → R) (D : Fin n → Derivation K R R)
    (hf : ∀ i, f i ∈ maximalIdeal R)
    (hdet : IsUnit (Matrix.det (fun i j => D i (f j)))) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range f)) := by
  classical
  let A : Matrix (Fin n) (Fin n) R := fun i j => D i (f j)
  let E : Fin n → Derivation K R R := fun i => ∑ k, (A⁻¹ i k) • D k
  have hE (i j : Fin n) : E i (f j) = if i = j then 1 else 0 := by
    calc
      E i (f j) = ∑ k, A⁻¹ i k * D k (f j) := by
        change (Derivation.coeFnAddMonoidHom (∑ k, A⁻¹ i k • D k)) (f j) = _
        rw [map_sum, Finset.sum_apply]
        simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
      _ = (A⁻¹ * A) i j := rfl
      _ = (1 : Matrix (Fin n) (Fin n) R) i j :=
        congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j)
          (Matrix.nonsing_inv_mul A hdet)
      _ = if i = j then 1 else 0 := Matrix.one_apply
  exact isRegularLocalRing_quotient_of_dual n R f E hf hE

end Derivation
