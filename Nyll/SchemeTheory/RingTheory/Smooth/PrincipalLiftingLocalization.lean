/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingAlgebra
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The principal lifting algebra away from its parameter

The divided syzygies follow from the original lifted equations after
inverting the parameter. Eliminating each new variable then gives an actual
equivalence with the localized polynomial algebra on the original variables.
-/

@[expose] public section

noncomputable section

universe u v w t z

namespace MvPolynomial

variable {R : Type u} {n : Type v} {m : Type w} {k : Type t}
  [CommRing R] [Fintype m]

/-- After inverting the parameter, the original lifted equations imply
every divided syzygy. -/
theorem principalLiftingIdeal_le_ker_of_isUnit
    {S : Type z} [CommRing S] [Algebra R S]
    (π : R) (f : m → MvPolynomial n R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, a s * f j = ∑ i, h s j i * f i + C (π ^ 2) * g s j)
    (φ : MvPolynomial (n ⊕ m) R →ₐ[R] S)
    (hπ : IsUnit (algebraMap R S π))
    (hf : ∀ j, φ (principalLiftingRelation π f j) = 0) :
    principalLiftingIdeal π f a h g ≤ RingHom.ker φ.toRingHom := by
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hf j
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, j⟩, rfl⟩
    have heq := congrArg φ (mul_principalLiftingSyzygy π f a h g hrel s j)
    simp only [map_mul, map_add, map_neg, map_sum, hf, mul_zero, neg_mul,
      Finset.sum_const_zero, zero_add, neg_zero, algHom_C] at heq
    exact hπ.mul_right_eq_zero.mp heq

/-- The actual principal lifting algebra becomes the original polynomial
algebra after inverting the parameter. The syzygy data impose no additional
equations on this open. -/
theorem nonempty_principalLifting_localization_equiv
    (π : R) (f : m → MvPolynomial n R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, a s * f j = ∑ i, h s j i * f i + C (π ^ 2) * g s j) :
    Nonempty
      (Localization.Away (algebraMap R
          (MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f a h g) π) ≃ₐ[R]
        Localization.Away (C π : MvPolynomial n R)) := by
  let J := principalLiftingIdeal π f a h g
  let D := MvPolynomial (n ⊕ m) R ⧸ J
  let Q := MvPolynomial n R
  let T := Localization.Away (C π : Q)
  let E := Localization.Away (algebraMap R D π)
  let q : MvPolynomial (n ⊕ m) R →ₐ[R] D := Ideal.Quotient.mkₐ R J
  let d : D →ₐ[R] E := IsScalarTower.toAlgHom R D E
  let c : Q →ₐ[R] T := IsScalarTower.toAlgHom R Q T
  have hπT : IsUnit (algebraMap R T π) := by
    change IsUnit (algebraMap Q T (C π))
    exact IsLocalization.Away.algebraMap_isUnit (C π : Q)
  have hπE : IsUnit (algebraMap R E π) := by
    rw [IsScalarTower.algebraMap_apply R D E]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R D π)
  let u : Tˣ := hπT.unit
  have hu : (u : T) = algebraMap R T π := hπT.unit_spec
  let v : n ⊕ m → T := Sum.elim (fun i => c (X i)) (fun j => (↑u⁻¹ : T) * c (f j))
  let φ : MvPolynomial (n ⊕ m) R →ₐ[R] T := aeval v
  have hφrename (p : Q) : φ (rename Sum.inl p) = c p := by
    rw [show φ = aeval v from rfl, aeval_rename]
    have heq : aeval (v ∘ Sum.inl) = c := by
      apply algHom_ext
      intro i
      exact aeval_X _ _
    rw [heq]
  have hφX (i : n ⊕ m) : φ (X i) = v i := aeval_X v i
  have hφf (j : m) : φ (principalLiftingRelation π f j) = 0 := by
    rw [principalLiftingRelation, map_sub, hφrename, map_mul, algHom_C, hφX]
    change c (f j) - algebraMap R T π * ((↑u⁻¹ : T) * c (f j)) = 0
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul, sub_self]
  let β : D →ₐ[R] T := Ideal.Quotient.liftₐ J φ
    (fun _ hx => principalLiftingIdeal_le_ker_of_isUnit π f a h g hrel φ hπT hφf hx)
  have hβ : β.comp q = φ := Ideal.Quotient.liftₐ_comp _ _ _
  have hβπ : IsUnit (β (algebraMap R D π)) := by
    rw [β.commutes]
    exact hπT
  let b : E →ₐ[R] T := IsLocalization.Away.liftAlgHom (algebraMap R D π) hβπ
  have hb (x : D) : b (d x) = β x :=
    IsLocalization.Away.lift_eq (algebraMap R D π) hβπ x
  let η : Q →ₐ[R] E := d.comp (q.comp (rename Sum.inl))
  have hηπ : IsUnit (η (C π)) := by
    rw [algHom_C]
    exact hπE
  let e : T →ₐ[R] E := IsLocalization.Away.liftAlgHom (C π : Q) hηπ
  have he (x : Q) : e (c x) = η x :=
    IsLocalization.Away.lift_eq (C π : Q) hηπ x
  have hbe : b.comp e = AlgHom.id R T := by
    apply IsLocalization.algHom_ext (.powers (C π : Q))
    apply algHom_ext
    intro i
    change b (e (c (X i))) = c (X i)
    rw [he, show η (X i) = d (q (rename Sum.inl (X i))) from rfl, hb]
    change (β.comp q) (rename Sum.inl (X i)) = c (X i)
    rw [hβ, hφrename]
  have heb : e.comp b = AlgHom.id R E := by
    apply IsLocalization.algHom_ext (.powers (algebraMap R D π))
    apply Ideal.Quotient.algHom_ext
    apply algHom_ext
    intro i
    change e (b (d (q (X i)))) = d (q (X i))
    rw [hb]
    change e ((β.comp q) (X i)) = d (q (X i))
    rw [hβ, hφX]
    cases i with
    | inl i =>
      change e (c (X i)) = d (q (X (Sum.inl i)))
      rw [he]
      exact congrArg (d ∘ q) (rename_X Sum.inl i)
    | inr j =>
      apply hπE.mul_left_cancel
      rw [← e.commutes, ← map_mul, e.commutes]
      change e (algebraMap R T π * ((↑u⁻¹ : T) * c (f j))) =
        algebraMap R E π * d (q (X (Sum.inr j)))
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul, he]
      have hj : q (principalLiftingRelation π f j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          ((show Ideal.span (Set.range (principalLiftingRelation π f)) ≤ J from
            le_sup_left) (Ideal.subset_span ⟨j, rfl⟩))
      rw [principalLiftingRelation, map_sub, sub_eq_zero, map_mul, algHom_C] at hj
      change d (q (rename Sum.inl (f j))) = _
      rw [hj, map_mul, d.commutes]
  exact ⟨AlgEquiv.ofAlgHom b e hbe heb⟩

/-- Away from the parameter, the actual lifting algebra is smooth over
the original base. -/
theorem smooth_principalLifting_localization [Finite n]
    (π : R) (f : m → MvPolynomial n R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, a s * f j = ∑ i, h s j i * f i + C (π ^ 2) * g s j) :
    Algebra.Smooth R (Localization.Away (algebraMap R
      (MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f a h g) π)) := by
  obtain ⟨e⟩ := nonempty_principalLifting_localization_equiv π f a h g hrel
  have : Algebra.Smooth R (MvPolynomial n R) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth (MvPolynomial n R) (Localization.Away (C π : MvPolynomial n R)) :=
    Algebra.Smooth.of_isLocalization_Away (C π : MvPolynomial n R)
  have : Algebra.Smooth R (Localization.Away (C π : MvPolynomial n R)) :=
    Algebra.Smooth.comp R (MvPolynomial n R) _
  exact Algebra.Smooth.of_equiv e.symm

end MvPolynomial
