/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.CoefficientFrobenius
public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.RingTheory.WittVector.Verschiebung
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Coefficient Frobenius differences at every Witt length

Surjectivity of an additive difference `f - 1` lifts to every finite Witt
length. The proof uses the actual Verschiebung and Teichmüller operations,
successively solving the constant coefficient. In particular, coefficient
Frobenius over an algebraic closure of a finite field is not restricted to
the prime-order Artin–Schreier calculation.
-/

@[expose] public section

noncomputable section

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

/-- A Witt vector with zero constant coefficient is in the actual
Verschiebung image. -/
theorem exists_verschiebung_eq_of_coeff_zero (y : WittVector p R)
    (hy : y.coeff 0 = 0) : ∃ z, verschiebung z = y := by
  refine ⟨WittVector.mk p (fun n => y.coeff (n + 1)), ?_⟩
  ext n
  cases n with
  | zero => exact hy.symm
  | succ n => rfl

/-- Equality through length `n` gives equality through length `n + 1`
after applying Verschiebung. -/
theorem truncate_verschiebung_eq_of_truncate_eq {n : ℕ}
    {x y : WittVector p R} (h : truncate n x = truncate n y) :
    truncate (n + 1) (verschiebung x) = truncate (n + 1) (verschiebung y) := by
  apply TruncatedWittVector.ext
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ i =>
    have hi' : i < n := Nat.lt_of_succ_lt_succ hi
    exact congrArg (TruncatedWittVector.coeff ⟨i, hi'⟩) h

/-- Surjectivity of `f - 1` on a ring implies surjectivity of the actual
Witt difference after truncation to any finite length. -/
theorem truncate_map_sub_id_surjective (f : R →+* R)
    (hf : Function.Surjective (fun x => f x - x)) (n : ℕ) :
    Function.Surjective (fun x : WittVector p R => truncate n (map f x - x)) := by
  let d : WittVector p R →+ WittVector p R :=
    (map f).toAddMonoidHom - AddMonoidHom.id _
  have hdV (x : WittVector p R) : d (verschiebung x) = verschiebung (d x) := by
    change map f (verschiebung x) - verschiebung x = verschiebung (map f x - x)
    rw [map_verschiebung, map_sub]
  have hsolve : ∀ n (y : WittVector p R), ∃ x, truncate n (d x) = truncate n y := by
    intro n
    induction n with
    | zero =>
      intro y
      refine ⟨0, ?_⟩
      apply TruncatedWittVector.ext
      exact fun i => Fin.elim0 i
    | succ n ih =>
      intro y
      obtain ⟨a, ha⟩ := hf (y.coeff 0)
      change f a - a = y.coeff 0 at ha
      let t := teichmuller p a
      have hz : (y - d t).coeff 0 = 0 := by
        change constantCoeff (y - (map f t - t)) = 0
        rw [map_sub, map_sub]
        change y.coeff 0 - (f a - a) = 0
        rw [ha, sub_self]
      obtain ⟨z, hz⟩ := exists_verschiebung_eq_of_coeff_zero (y - d t) hz
      obtain ⟨x, hx⟩ := ih z
      refine ⟨t + verschiebung x, ?_⟩
      have hy : y = d t + verschiebung z := by
        rw [hz, add_sub_cancel]
      change truncate (n + 1) (d (t + verschiebung x)) = _
      rw [map_add, hdV, hy, map_add, map_add]
      exact congrArg (fun a => truncate (n + 1) (d t) + a)
        (truncate_verschiebung_eq_of_truncate_eq hx)
  intro y
  obtain ⟨z, rfl⟩ := truncate_surjective p n R y
  exact hsolve n z

end WittVector

open scoped TensorProduct

namespace FiniteField

variable (k Ω R : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω] [CommRing R] [Algebra k R]

/-- Coefficient Frobenius minus the identity is surjective at every finite
Witt length, on any coordinate ring extended from the finite field. -/
theorem coefficientFrobenius_witt_sub_id_surjective (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    Function.Surjective (fun x : WittVector p (R ⊗[k] Ω) =>
      WittVector.truncate m
        (WittVector.map (coefficientFrobenius k Ω R n).toRingHom x - x)) :=
  WittVector.truncate_map_sub_id_surjective _
    (coefficientFrobenius_sub_id_surjective k Ω R n hn) m

end FiniteField
