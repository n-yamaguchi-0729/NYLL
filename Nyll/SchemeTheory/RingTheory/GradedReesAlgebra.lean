/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Basic

/-!
# The native grading of the Rees algebra

The actual polynomial subalgebra `reesAlgebra I` is the direct sum of its
homogeneous monomials with coefficients in the powers of `I`. The grading
is constructed from polynomial coefficients, without freeness or regularity
of the ideal. It supplies the graded algebra used by the Proj construction
of an affine blowup (Stacks Project, Section 31.33).
-/

noncomputable section

universe u

open Polynomial DirectSum

namespace ReesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The degree `n` monomial with an actual coefficient in `I ^ n`. -/
def monomial (n : ℕ) : ↥(I ^ n) →ₗ[R] reesAlgebra I where
  toFun r := ⟨Polynomial.monomial n r.val, reesAlgebra.monomial_mem.mpr r.property⟩
  map_add' r s := Subtype.ext ((Polynomial.monomial n).map_add r.val s.val)
  map_smul' r s := Subtype.ext ((Polynomial.monomial n).map_smul r s.val)

/-- The native homogeneous degree `n` submodule of the Rees algebra. -/
def homogeneousPart (n : ℕ) : Submodule R (reesAlgebra I) := (monomial I n).range

/-- The actual degree `n` component of an element of the Rees algebra. -/
def component (p : reesAlgebra I) (n : ℕ) : homogeneousPart I n :=
  ⟨monomial I n ⟨p.val.coeff n, p.property n⟩, ⟨⟨p.val.coeff n, p.property n⟩, rfl⟩⟩

lemma homogeneousPart_monomial_coeff (n : ℕ) (x : homogeneousPart I n) :
    x.val.val = Polynomial.monomial n (x.val.val.coeff n) := by
  obtain ⟨r, hr⟩ := x.property
  have hx : x.val.val = Polynomial.monomial n r.val :=
    congrArg (fun p : reesAlgebra I => p.val) hr.symm
  rw [hx, Polynomial.coeff_monomial_same]

lemma homogeneousPart_coeff (n m : ℕ) (x : homogeneousPart I n) :
    x.val.val.coeff m = if n = m then x.val.val.coeff n else 0 :=
  (congrArg (fun p : R[X] => p.coeff m) (homogeneousPart_monomial_coeff I n x)).trans
    (Polynomial.coeff_monomial (n := n) (a := x.val.val.coeff n) (m := m))

private lemma component_coeff (p : reesAlgebra I) (n : ℕ) :
    (component I p n).val.val.coeff n = p.val.coeff n :=
  Polynomial.coeff_monomial_same n _

private lemma coefficient_sum (x : ⨁ n, homogeneousPart I n) (n : ℕ) :
    (DirectSum.coeAddMonoidHom (homogeneousPart I) x).val.coeff n =
      (x n).val.val.coeff n := by
  induction x using DirectSum.induction_on with
  | zero => rfl
  | of m x =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : m = n
    · subst m
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne (β := fun n => ↥(homogeneousPart I n)) m n x (Ne.symm h)]
      exact (homogeneousPart_coeff I m n x).trans (ite_eq_right h)
  | add x y hx hy =>
    simp only [map_add, Subalgebra.coe_add, Polynomial.coeff_add, DirectSum.add_apply,
      Submodule.coe_add, hx, hy]

private def decomposition (p : reesAlgebra I) : ⨁ n, homogeneousPart I n :=
  DirectSum.mk (fun n => homogeneousPart I n) p.val.support
    (fun n => component I p n.val)

private lemma decomposition_apply (p : reesAlgebra I) (n : ℕ) :
    decomposition I p n = component I p n := by
  classical
  by_cases hn : n ∈ p.val.support
  · exact DirectSum.mk_apply_of_mem hn
  · have hp : p.val.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    rw [decomposition, DirectSum.mk_apply_of_notMem hn]
    apply Subtype.ext
    apply Subtype.ext
    change 0 = Polynomial.monomial n (p.val.coeff n)
    rw [hp, map_zero]

private lemma decomposition_leftInverse :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (homogeneousPart I)) (decomposition I) := by
  intro p
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  rw [coefficient_sum, decomposition_apply, component_coeff]

private lemma decomposition_rightInverse :
    Function.RightInverse (DirectSum.coeAddMonoidHom (homogeneousPart I)) (decomposition I) := by
  intro x
  apply DFinsupp.ext
  intro n
  rw [decomposition_apply]
  apply Subtype.ext
  apply Subtype.ext
  change Polynomial.monomial n
      ((DirectSum.coeAddMonoidHom (homogeneousPart I) x).val.coeff n) = (x n).val.val
  rw [coefficient_sum]
  exact (homogeneousPart_monomial_coeff I n (x n)).symm

instance : SetLike.GradedMonoid (homogeneousPart I) where
  one_mem := by
    let r : ↥(I ^ 0) := ⟨1, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact Polynomial.monomial_zero_left.trans (map_one Polynomial.C)
  mul_mem := by
    intro n m x y hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hab : a.val * b.val ∈ I ^ (n + m) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul a.property b.property
    refine ⟨⟨a.val * b.val, hab⟩, ?_⟩
    apply Subtype.ext
    exact (Polynomial.monomial_mul_monomial n m a.val b.val).symm

/-- The Rees algebra has its actual nonnegative grading by ideal powers. -/
instance gradedAlgebra : GradedAlgebra (homogeneousPart I) where
  __ := (inferInstance : SetLike.GradedMonoid (homogeneousPart I))
  decompose' := decomposition I
  left_inv := decomposition_leftInverse I
  right_inv := decomposition_rightInverse I

/-- The actual degree-zero part of the Rees algebra is the coefficient ring. -/
def degreeZeroEquiv : R ≃+* homogeneousPart I 0 where
  toFun r := ⟨algebraMap R (reesAlgebra I) r, by
    let a : ↥(I ^ 0) := ⟨r, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change Polynomial.monomial 0 r = Polynomial.C r
    exact Polynomial.monomial_zero_left (R := R) (a := r)⟩
  invFun x := x.val.val.coeff 0
  left_inv r := Polynomial.coeff_C_zero
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change Polynomial.C (x.val.val.coeff 0) = x.val.val
    exact Polynomial.monomial_zero_left.symm.trans
      (homogeneousPart_monomial_coeff I 0 x).symm
  map_add' r s := Subtype.ext (map_add (algebraMap R (reesAlgebra I)) r s)
  map_mul' r s := Subtype.ext (map_mul (algebraMap R (reesAlgebra I)) r s)

/-- Finite generation of the ideal makes its actual Rees algebra of finite
type over its degree-zero part, with no Noetherian hypothesis on the ring. -/
theorem finiteType_degreeZero (hI : I.FG) :
    Algebra.FiniteType (homogeneousPart I 0) (reesAlgebra I) := by
  obtain ⟨s, hs⟩ := (reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)
  refine ⟨⟨s, ?_⟩⟩
  apply top_unique
  intro x _
  have hx : x ∈ Algebra.adjoin R (s : Set (reesAlgebra I)) := by
    rw [hs]
    exact Algebra.mem_top
  refine Algebra.adjoin_induction (R := R)
    (p := fun x _ => x ∈ Algebra.adjoin (homogeneousPart I 0) (s : Set (reesAlgebra I)))
    (fun x hx => Algebra.subset_adjoin hx) (fun r => ?_)
    (fun x y _ _ hx hy => Subalgebra.add_mem _ hx hy)
    (fun x y _ _ hx hy => Subalgebra.mul_mem _ hx hy) hx
  exact (Algebra.adjoin (homogeneousPart I 0) (s : Set (reesAlgebra I))).algebraMap_mem
    (degreeZeroEquiv I r)

end ReesAlgebra
