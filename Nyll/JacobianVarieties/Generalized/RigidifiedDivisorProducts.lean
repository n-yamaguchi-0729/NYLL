/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorTensor
import Nyll.JacobianVarieties.Generalized.RigidifiedCommutativity
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Powers and finite products of canonically rigidified divisor ideals -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X)

/-- The empty effective divisor gives the identity rigidified class. -/
theorem classOf_ofInvertibleIdeal_top
    (hI : (⊤ : X.IdealSheafData).IsInvertible)
    (ha : ∀ y : D, i.base y ∉ (⊤ : X.IdealSheafData).support) :
    classOf (ofInvertibleIdeal i ⊤ hI ha) = 1 := by
  have h : classOf (ofInvertibleIdeal i ⊤ hI ha) =
      classOf (ofInvertibleIdeal i ⊤ hI ha) * classOf (ofInvertibleIdeal i ⊤ hI ha) := by
    simpa only [Scheme.IdealSheafData.top_mul] using
      classOf_ofInvertibleIdeal_mul i ⊤ ⊤ hI hI ha ha
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

/-- Every nonnegative power of a disjoint ideal stays disjoint from the modulus. -/
theorem avoids_pow (I : X.IdealSheafData)
    (ha : ∀ y : D, i.base y ∉ I.support) (n : ℕ) :
    ∀ y : D, i.base y ∉ (I ^ n).support := by
  cases n with
  | zero =>
    intro y
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
    exact fun h => h
  | succ n =>
    rw [Scheme.IdealSheafData.support_pow_succ]
    exact ha

/-- Repeated divisor addition agrees with powers in the actual rigidified class group. -/
theorem classOf_ofInvertibleIdeal_pow (I : X.IdealSheafData) (hI : I.IsInvertible)
    (ha : ∀ y : D, i.base y ∉ I.support) (n : ℕ) :
    classOf (ofInvertibleIdeal i (I ^ n) (hI.pow n) (avoids_pow i I ha n)) =
      classOf (ofInvertibleIdeal i I hI ha) ^ n := by
  induction n with
  | zero =>
    simpa only [pow_zero, Scheme.IdealSheafData.one_eq_top] using
      classOf_ofInvertibleIdeal_top i Scheme.IdealSheafData.isInvertible_top
        (fun y h => h)
  | succ n ih =>
    have h :
        classOf (ofInvertibleIdeal i (I ^ (n + 1)) (hI.pow (n + 1))
          (avoids_pow i I ha (n + 1))) =
        classOf (ofInvertibleIdeal i (I ^ n) (hI.pow n) (avoids_pow i I ha n)) *
          classOf (ofInvertibleIdeal i I hI ha) := by
      simpa only [pow_succ] using
        classOf_ofInvertibleIdeal_mul i (I ^ n) I (hI.pow n) hI
          (avoids_pow i I ha n) ha
    rw [h, ih, pow_succ]

/-- The product ideal of finitely many Cartier ideals is Cartier. -/
theorem isInvertible_finset_prod {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (hI : ∀ a, (I a).IsInvertible) :
    (∏ a ∈ s, I a).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact Scheme.IdealSheafData.isInvertible_top
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hI a).mul ih

/-- A finite product of ideals away from the modulus stays away from it. -/
theorem avoids_finset_prod {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (ha : ∀ a, ∀ y : D, i.base y ∉ (I a).support) :
    ∀ y : D, i.base y ∉ (∏ a ∈ s, I a).support := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.support_top]
    exact fun h => h
  | @insert a s hs ih =>
    rw [Finset.prod_insert hs]
    exact avoids_mul i (I a) (∏ b ∈ s, I b) (ha a) ih

/-- Canonical rigidification turns finite products of ideals into products of classes. -/
theorem classOf_ofInvertibleIdeal_finset_prod {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (hI : ∀ a, (I a).IsInvertible)
    (ha : ∀ a, ∀ y : D, i.base y ∉ (I a).support) :
    classOf (ofInvertibleIdeal i (∏ a ∈ s, I a) (isInvertible_finset_prod s I hI)
      (avoids_finset_prod i s I ha)) =
      ∏ a ∈ s, classOf (ofInvertibleIdeal i (I a) (hI a) (ha a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top] using
      classOf_ofInvertibleIdeal_top i Scheme.IdealSheafData.isInvertible_top
        (fun y h => h)
  | @insert a s hs ih =>
    have h :
        classOf (ofInvertibleIdeal i (∏ b ∈ insert a s, I b)
          (isInvertible_finset_prod (insert a s) I hI)
          (avoids_finset_prod i (insert a s) I ha)) =
        classOf (ofInvertibleIdeal i (I a) (hI a) (ha a)) *
          classOf (ofInvertibleIdeal i (∏ b ∈ s, I b)
            (isInvertible_finset_prod s I hI) (avoids_finset_prod i s I ha)) := by
      simpa only [Finset.prod_insert hs] using
        classOf_ofInvertibleIdeal_mul i (I a) (∏ b ∈ s, I b)
          (hI a) (isInvertible_finset_prod s I hI) (ha a) (avoids_finset_prod i s I ha)
    rw [h, ih, Finset.prod_insert hs]

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
