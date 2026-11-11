/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingAlgebra

/-!
# The cross identity for the principal lifting syzygies

This polynomial identity compares two of the original divided-syzygy families.
It requires no relation-ideal or localization hypothesis.
-/

@[expose] public section

namespace MvPolynomial

private theorem syzygy_cross_identity
    {S m k : Type*} [CommRing S] [Fintype m]
    (d : S) (a : k → S) (h : k → m → m → S) (g : k → m → S)
    (z : m → S) (s t : k) (j : m) :
    a t * (a s * z j - ∑ i, h s j i * z i - d * g s j) -
        a s * (a t * z j - ∑ i, h t j i * z i - d * g t j) +
        (∑ i, h s j i * (a t * z i - ∑ l, h t i l * z l - d * g t i)) =
      (∑ l, (a s * h t j l - ∑ i, h s j i * h t i l) * z l) +
        d * (-a t * g s j + a s * g t j - ∑ i, h s j i * g t i) := by
  have hfactor (c : S) (v : m → S) :
      (∑ i, h s j i * (c * v i)) = c * ∑ i, h s j i * v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdouble :
      (∑ i, h s j i * ∑ l, h t i l * z l) =
        ∑ l, (∑ i, h s j i * h t i l) * z l := by
    calc
      _ = ∑ i, ∑ l, h s j i * (h t i l * z l) := by
        simp only [Finset.mul_sum]
      _ = ∑ l, ∑ i, h s j i * (h t i l * z l) := Finset.sum_comm
      _ = _ := by simp only [Finset.sum_mul, mul_assoc]
  have hcoeff :
      (∑ l, (a s * h t j l - ∑ i, h s j i * h t i l) * z l) =
        a s * (∑ l, h t j l * z l) -
          ∑ i, h s j i * ∑ l, h t i l * z l := by
    rw [hdouble]
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [hcoeff]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hfactor (a t) z, hfactor d (g t)]
  ring

/-- The exact cross-family identity in the original lifting polynomial ring.
All coefficient polynomials are renamed along the original-variable inclusion. -/
theorem principalLiftingSyzygy_cross
    {R n m k : Type*} [CommRing R] [Fintype m]
    (π : R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (s t : k) (j : m) :
    rename Sum.inl (a t) * principalLiftingSyzygy π a h g s j -
        rename Sum.inl (a s) * principalLiftingSyzygy π a h g t j +
        (∑ i, rename Sum.inl (h s j i) * principalLiftingSyzygy π a h g t i) =
      (∑ l, rename Sum.inl (a s * h t j l - ∑ i, h s j i * h t i l) *
        X (Sum.inr l)) +
        C π * rename Sum.inl
          (-a t * g s j + a s * g t j - ∑ i, h s j i * g t i) := by
  simpa only [principalLiftingSyzygy, map_sub, map_mul, map_sum, map_add, map_neg] using
    syzygy_cross_identity (C π) (fun i => rename Sum.inl (a i))
      (fun r i l => rename Sum.inl (h r i l)) (fun r i => rename Sum.inl (g r i))
      (fun i => X (Sum.inr i)) s t j

end MvPolynomial
