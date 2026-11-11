/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.JacobianLocalization
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingAlgebra
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Smooth selected charts in the principal lifting construction

Use the selected old variables and the complementary new variables as
Jacobian coordinates. With the native variable-row convention the lower-left
block is zero and the lower-right block is the diagonal matrix with entry A.
This identity holds before taking residues. A unit original minor and a unit
A therefore give an actual standard-smooth Jacobian localization preserving
the supplied target map.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {R n m κ : Type*} [CommRing R] [Fintype κ]

/-- The selected original lifting equations and the complementary divided
syzygies, retaining their original polynomial coefficients. -/
def principalLiftingChartRelations (π : R) (f : m → MvPolynomial n R)
    (a : κ → m) (A : MvPolynomial n R)
    (h : {j : m // j ∉ Set.range a} → κ → MvPolynomial n R)
    (g : {j : m // j ∉ Set.range a} → MvPolynomial n R) :
    (κ ⊕ {j : m // j ∉ Set.range a}) → MvPolynomial (n ⊕ m) R :=
  Sum.elim (fun i => principalLiftingRelation π f (a i))
    (fun l => rename Sum.inl A * X (Sum.inr l.val) -
      ∑ i, rename Sum.inl (h l i) * X (Sum.inr (a i)) - C π * rename Sum.inl (g l))

private theorem pderiv_inr_rename_inl (j : m) (p : MvPolynomial n R) :
    pderiv (Sum.inr j) (rename (Sum.inl : n → n ⊕ m) p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [rename_C, pderiv_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    rw [map_mul, rename_X, pderiv_mul, hp, zero_mul,
      pderiv_X_of_ne Sum.inl_ne_inr, mul_zero, add_zero]

omit [Fintype κ] in
/-- The normalized rows belonging to selected original relations are literal
zero polynomials in the full lifting system. -/
theorem principalLiftingSyzygy_selected_eq_zero
    {k : Type*} [Fintype m] [DecidableEq m]
    (π : R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (t : k) (a : κ → m)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hzero : ∀ i, g t (a i) = 0) (i : κ) :
    principalLiftingSyzygy π A H g t (a i) = 0 := by
  rw [principalLiftingSyzygy, hzero, map_zero, mul_zero, sub_zero]
  simp only [hdiag, apply_ite, map_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]

/-- In the selected chart, the original identities and the unit parameter
force all original lifting equations and all syzygies from the selected
family to vanish, including the equations omitted from the chart. -/
theorem principalLifting_equations_zero_of_chart
    {k L : Type*} [Fintype m] [DecidableEq m]
    [CommRing L] [Algebra R L]
    (π : R) (f : m → MvPolynomial n R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ i, H s j i * f i + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hzero : ∀ i, g t (a i) = 0)
    (φ : MvPolynomial (n ⊕ m) R →ₐ[R] L)
    (hchart : ∀ u, φ (principalLiftingChartRelations π f a (A t)
      (fun l i => H t l.val (a i)) (fun l => g t l.val) u) = 0)
    (hA : IsUnit (φ (rename Sum.inl (A t)))) :
    (∀ j, φ (principalLiftingRelation π f j) = 0) ∧
      ∀ j, φ (principalLiftingSyzygy π A H g t j) = 0 := by
  have hsum (j : m) :
      (∑ l, rename (Sum.inl : n → n ⊕ m) (H t j l) * X (Sum.inr l)) =
        ∑ i, rename Sum.inl (H t j (a i)) * X (Sum.inr (a i)) := by
    symm
    apply Fintype.sum_of_injective a ha
    · intro l hl
      rw [hsupport j l hl, map_zero, zero_mul]
    · intro i
      rfl
  have hp (j : m) : φ (principalLiftingSyzygy π A H g t j) = 0 := by
    by_cases hj : j ∈ Set.range a
    · obtain ⟨i, rfl⟩ := hj
      rw [principalLiftingSyzygy_selected_eq_zero π A H g t a hdiag hzero i, map_zero]
    · change φ (rename Sum.inl (A t) * X (Sum.inr j) -
        ∑ l, rename Sum.inl (H t j l) * X (Sum.inr l) -
          C π * rename Sum.inl (g t j)) = 0
      rw [hsum]
      exact hchart (Sum.inr ⟨j, hj⟩)
  refine ⟨?_, hp⟩
  intro j
  have hsumzero : (∑ l, φ (rename Sum.inl (H t j l)) *
      φ (principalLiftingRelation π f l)) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ∈ Set.range a
    · obtain ⟨i, rfl⟩ := hl
      rw [show φ (principalLiftingRelation π f (a i)) = 0 from hchart (Sum.inl i),
        mul_zero]
    · rw [hsupport j l hl, map_zero, map_zero, zero_mul]
  have hid := congrArg φ (mul_principalLiftingSyzygy π f A H g hrel t j)
  simp only [map_mul, map_add, map_neg, map_sum, hp, mul_zero, hsumzero, add_zero]
    at hid
  apply hA.mul_right_eq_zero.mp
  exact neg_eq_zero.mp (by simpa only [neg_mul] using hid.symm)

end MvPolynomial

open MvPolynomial

namespace Algebra

/-- The actual selected chart has a standard-smooth localization through
which the original target map factors. Its Jacobian unit follows from the
original selected minor and A, with no locality hypothesis on the target. -/
theorem exists_standardSmooth_localization_of_principalLiftingChart
    {R L n m κ : Type*} [CommRing R] [CommRing L] [Algebra R L]
    [Finite n] [Finite m] [Fintype κ] [DecidableEq κ]
    (π : R) (f : m → MvPolynomial n R) (a : κ → m)
    (b : κ → n) (hb : Function.Injective b) (A : MvPolynomial n R)
    (h : {j : m // j ∉ Set.range a} → κ → MvPolynomial n R)
    (g : {j : m // j ∉ Set.range a} → MvPolynomial n R)
    (β : (MvPolynomial (n ⊕ m) R ⧸
      Ideal.span (Set.range (principalLiftingChartRelations π f a A h g))) →ₐ[R] L)
    (hA : IsUnit (β (Ideal.Quotient.mk _ (rename Sum.inl A))))
    (hminor : IsUnit (β (Ideal.Quotient.mk _ (rename Sum.inl
      (Matrix.of (fun j i => pderiv (b i) (f (a j)))).det)))) :
    ∃ d : MvPolynomial (n ⊕ m) R ⧸
        Ideal.span (Set.range (principalLiftingChartRelations π f a A h g)),
      IsStandardSmooth R (Localization.Away d) ∧
        ∃ γ : Localization.Away d →ₐ[R] L,
          γ.comp (IsScalarTower.toAlgHom R _ (Localization.Away d)) = β := by
  classical
  let c := {j : m // j ∉ Set.range a}
  let _ : Fintype c := Fintype.ofFinite c
  let G := principalLiftingChartRelations π f a A h g
  let Q := MvPolynomial (n ⊕ m) R ⧸ Ideal.span (Set.range G)
  let P : PreSubmersivePresentation R Q (n ⊕ m) (κ ⊕ c) :=
    { toPresentation := Presentation.naive
      map := Sum.elim (fun i => Sum.inl (b i)) (fun l => Sum.inr l.val)
      map_inj := Sum.elim_injective.mpr
        ⟨Sum.inl_injective.comp hb, Sum.inr_injective.comp Subtype.val_injective,
          fun _ _ => Sum.inl_ne_inr⟩ }
  let φ : MvPolynomial (n ⊕ m) R →+* L :=
    β.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range G)))
  let ψ : MvPolynomial n R →+* L := φ.comp (rename Sum.inl).toRingHom
  let M : Matrix κ κ (MvPolynomial n R) :=
    Matrix.of fun j i => pderiv (b i) (f (a j))
  let U : Matrix κ c L := fun i l => φ (pderiv (Sum.inl (b i)) (G (Sum.inr l)))
  have hcross (l : c) (i : κ) :
      pderiv (Sum.inr l.val) (X (Sum.inr (a i)) : MvPolynomial (n ⊕ m) R) = 0 :=
    pderiv_X_of_ne (fun he => l.property ⟨i, Sum.inr.inj he⟩)
  have hsum (l l' : c) :
      pderiv (Sum.inr l.val)
        (∑ i, rename Sum.inl (h l' i) * X (Sum.inr (a i))) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [pderiv_mul, MvPolynomial.pderiv_inr_rename_inl, zero_mul, zero_add,
      hcross, mul_zero]
  have hright (l l' : c) :
      pderiv (Sum.inr l.val) (G (Sum.inr l')) =
        rename Sum.inl A * pderiv (Sum.inr l.val) (X (Sum.inr l'.val)) := by
    change pderiv (Sum.inr l.val)
      (rename Sum.inl A * X (Sum.inr l'.val) -
        ∑ i, rename Sum.inl (h l' i) * X (Sum.inr (a i)) -
          C π * rename Sum.inl (g l')) = _
    rw [map_sub, map_sub, pderiv_mul, MvPolynomial.pderiv_inr_rename_inl,
      zero_mul, zero_add, hsum, sub_zero, pderiv_mul, pderiv_C,
      zero_mul, MvPolynomial.pderiv_inr_rename_inl, mul_zero, add_zero, sub_zero]
  have hmatrix : φ.mapMatrix P.jacobiMatrix =
      Matrix.fromBlocks (ψ.mapMatrix M).transpose U 0
        (Matrix.diagonal (fun _ : c => ψ A)) := by
    apply Matrix.ext
    intro i j
    change φ (P.jacobiMatrix i j) = _
    rw [P.jacobiMatrix_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change φ (pderiv (Sum.inl (b i)) (principalLiftingRelation π f (a j))) =
          ψ (pderiv (b i) (f (a j)))
        rw [principalLiftingRelation, map_sub, pderiv_rename Sum.inl_injective,
          pderiv_mul, pderiv_C, zero_mul, zero_add,
          pderiv_X_of_ne Sum.inr_ne_inl, mul_zero, sub_zero]
        rfl
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        change φ (pderiv (Sum.inr i.val) (principalLiftingRelation π f (a j))) = 0
        rw [principalLiftingRelation, map_sub, MvPolynomial.pderiv_inr_rename_inl,
          pderiv_mul, pderiv_C, zero_mul, zero_add, hcross, mul_zero,
          sub_zero, map_zero]
      | inr j =>
        change φ (pderiv (Sum.inr i.val) (G (Sum.inr j))) =
          Matrix.diagonal (fun _ : c => ψ A) i j
        rw [hright]
        by_cases hij : i = j
        · subst j
          rw [pderiv_X_self, mul_one, Matrix.diagonal_apply_eq]
          rfl
        · rw [pderiv_X_of_ne (fun he => hij (Subtype.ext (Sum.inr.inj he).symm)),
            mul_zero, map_zero, Matrix.diagonal_apply_ne _ hij]
  have hminor' : IsUnit (ψ M.det) := hminor
  have hA' : IsUnit (ψ A) := hA
  have hunit : IsUnit (β P.jacobian) := by
    rw [P.jacobian_eq_jacobiMatrix_det]
    change IsUnit (φ P.jacobiMatrix.det)
    rw [RingHom.map_det, hmatrix, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_transpose, Matrix.det_diagonal, ← RingHom.map_det]
    exact hminor'.mul (IsUnit.prod_univ_iff.mpr fun _ => hA')
  refine ⟨P.jacobian, P.jacobianLocalizationPresentation.isStandardSmooth,
    IsLocalization.Away.liftAlgHom P.jacobian hunit, ?_⟩
  apply AlgHom.ext
  intro q
  exact IsLocalization.Away.lift_eq P.jacobian hunit q

end Algebra
