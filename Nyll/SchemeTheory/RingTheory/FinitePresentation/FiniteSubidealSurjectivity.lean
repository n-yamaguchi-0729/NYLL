/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Surjectivity at an actual finite subideal

If a finite-type algebra becomes a quotient of the base ring after imposing
an arbitrary ideal, finitely many relations already make it a quotient.
The relations compare the original finite algebra generators with actual
chosen lifts from the base ring. This is the affine ingredient for common
finite-presentation closed refinements of two closed ambient models.
-/

@[expose] public section

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Surjectivity onto an arbitrary quotient of a finite-type algebra is
already witnessed by a finitely generated subideal of its defining ideal. -/
theorem exists_fg_subideal_surjective_quotient [FiniteType R S]
    (I : Ideal S) (h : Function.Surjective (algebraMap R (S ⧸ I))) :
    ∃ J : Ideal S, J ≤ I ∧ J.FG ∧
      Function.Surjective (algebraMap R (S ⧸ J)) := by
  classical
  obtain ⟨s, hs⟩ := FiniteType.out (R := R) (A := S)
  choose a ha using fun x : s => h (Ideal.Quotient.mk I x.1)
  let d : s → S := fun x => x.1 - algebraMap R S (a x)
  let J : Ideal S := Ideal.span (Set.range d)
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk I (x.1 - algebraMap R S (a x)) = 0
    rw [map_sub, Ideal.Quotient.mk_algebraMap, ha, sub_self]
  refine ⟨J, hJI, Submodule.fg_span (Set.finite_range d), ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hx : x ∈ Algebra.adjoin R (s : Set S) := by
    rw [hs]
    exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      refine ⟨a ⟨x, hx⟩, ?_⟩
      apply Eq.symm
      apply sub_eq_zero.mp
      rw [← Ideal.Quotient.mk_algebraMap, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩)
  | algebraMap r =>
      exact ⟨r, (Ideal.Quotient.mk_algebraMap R J r).symm⟩
  | add x y _ _ hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by rw [map_add, map_add, hr, hs]⟩
  | mul x y _ _ hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r * s, by rw [map_mul, map_mul, hr, hs]⟩

end Algebra
