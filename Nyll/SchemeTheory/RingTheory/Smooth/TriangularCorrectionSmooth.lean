/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.JacobianLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smooth correction algebras at an actual local target

A finite system whose reduction is triangular linear has an actual
Jacobian localization which is standard smooth. Every map to a local
target in which the reduction parameter is nonunit extends to this
localization. The unit Jacobian is proved by its actual residue matrix.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace Algebra

/-- A triangular reduction produces a standard smooth localization and
the factorization of the supplied map to its original local target. -/
theorem exists_standardSmooth_localization_of_triangular_relations
    {R L m n : Type*} [CommRing R] [CommRing L] [Algebra R L]
    [IsLocalRing L] [Finite m] [Fintype n]
    (π : R) (r : Matrix m n R) (g : m → MvPolynomial (m ⊕ n) R)
    (hg : ∀ j, C π ∣ g j -
      (X (Sum.inl j) + ∑ i, C (r j i) * X (Sum.inr i)))
    (β : (MvPolynomial (m ⊕ n) R ⧸ Ideal.span (Set.range g)) →ₐ[R] L)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L) :
    ∃ d : MvPolynomial (m ⊕ n) R ⧸ Ideal.span (Set.range g),
      IsStandardSmooth R (Localization.Away d) ∧
        ∃ γ : Localization.Away d →ₐ[R] L,
          γ.comp (IsScalarTower.toAlgHom R
            (MvPolynomial (m ⊕ n) R ⧸ Ideal.span (Set.range g))
            (Localization.Away d)) = β := by
  classical
  let _ : Fintype m := Fintype.ofFinite m
  let Q := MvPolynomial (m ⊕ n) R ⧸ Ideal.span (Set.range g)
  let P : PreSubmersivePresentation R Q (m ⊕ n) m :=
    { toPresentation := Presentation.naive
      map := Sum.inl
      map_inj := Sum.inl_injective }
  let φ : MvPolynomial (m ⊕ n) R →+* IsLocalRing.ResidueField L :=
    (IsLocalRing.residue L).comp
      (β.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range g))))
  have hφπ : φ (C π) = 0 := by
    change IsLocalRing.residue L (β (algebraMap R Q π)) = 0
    rw [β.commutes]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hπ
  have hcross (i j : m) :
      pderiv (Sum.inl i) (∑ k : n, C (r j k) * X (Sum.inr k)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _hk
    rw [pderiv_mul, pderiv_C, zero_mul, zero_add,
      pderiv_X_of_ne Sum.inr_ne_inl, mul_zero]
  have hderiv (i j : m) :
      φ (pderiv (Sum.inl i) (g j)) = φ (pderiv (Sum.inl i) (X (Sum.inl j))) := by
    obtain ⟨q, hq⟩ := hg j
    have h := congrArg (pderiv (Sum.inl i)) hq
    rw [map_sub, map_add, hcross, add_zero, pderiv_mul,
      pderiv_C, zero_mul, zero_add] at h
    have hh := congrArg φ h
    rw [map_sub, map_mul, hφπ, zero_mul] at hh
    exact sub_eq_zero.mp hh
  have hmatrix : φ.mapMatrix P.jacobiMatrix =
      (1 : Matrix m m (IsLocalRing.ResidueField L)) := by
    apply Matrix.ext
    intro i j
    change φ (P.jacobiMatrix i j) = (1 : Matrix m m _) i j
    rw [P.jacobiMatrix_apply]
    change φ (pderiv (Sum.inl i) (g j)) = (1 : Matrix m m _) i j
    rw [hderiv]
    by_cases hij : i = j
    · subst j
      rw [pderiv_X_self, map_one, Matrix.one_apply, ite_eq_left rfl]
    · rw [pderiv_X_of_ne (fun h => hij (Sum.inl.inj h).symm),
        map_zero, Matrix.one_apply, ite_eq_right hij]
  have hres : IsLocalRing.residue L (β P.jacobian) = 1 := by
    rw [P.jacobian_eq_jacobiMatrix_det]
    change φ P.jacobiMatrix.det = 1
    rw [RingHom.map_det, hmatrix, Matrix.det_one]
  have hunit : IsUnit (β P.jacobian) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [hres]
    exact one_ne_zero
  refine ⟨P.jacobian, P.jacobianLocalizationPresentation.isStandardSmooth,
    IsLocalization.Away.liftAlgHom P.jacobian hunit, ?_⟩
  apply AlgHom.ext
  intro q
  exact IsLocalization.Away.lift_eq P.jacobian hunit q

end Algebra
