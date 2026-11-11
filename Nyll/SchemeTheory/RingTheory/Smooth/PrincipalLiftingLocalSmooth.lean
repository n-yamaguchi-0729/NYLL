/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingSmoothChart
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingMinorSelection
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Smooth neighborhoods in the principal lifting algebra over a local target

The target maximal ideal pulls back to an ideal containing every original
relation and the square parameter. Actual strictly-standard membership then
selects an original Jacobian minor whose target image is a unit. This gives
a smooth neighborhood of the full lifting algebra retaining its target map.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace Algebra

/-- A chosen strictly-standard parameter which is a unit in the original
local target supplies a smooth neighborhood of the full lifting algebra.
The original minor, chart flatness, and comparison are all constructed. -/
theorem exists_smooth_localization_of_principalLifting_strictStandard
    {R L n m k κ : Type*} [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [Finite n] [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]
    (π : R) (hstable : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    {B : Type*} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hP : ∀ j, P.relation j = map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j))
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ i, H s j i * f i + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hzero : ∀ i, g t (a i) = 0)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det))
    (β : (MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f A H g) →ₐ[R] L)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L)
    (hA : IsUnit (β (Ideal.Quotient.mk _ (rename Sum.inl (A t))))) :
    ∃ d : MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f A H g,
      Smooth R (Localization.Away d) ∧ IsUnit (β d) ∧
        ∃ γ : Localization.Away d →ₐ[R] L,
          γ.comp (IsScalarTower.toAlgHom R _ (Localization.Away d)) = β := by
  let J := principalLiftingIdeal π f A H g
  let D := MvPolynomial (n ⊕ m) R ⧸ J
  let q : MvPolynomial (n ⊕ m) R →ₐ[R] D := Ideal.Quotient.mkₐ R J
  let φ : MvPolynomial (n ⊕ m) R →ₐ[R] L := β.comp q
  let ψ : MvPolynomial n R →ₐ[R] L := φ.comp (rename Sum.inl)
  let p : Ideal (MvPolynomial n R) :=
    (IsLocalRing.maximalIdeal L).comap ψ.toRingHom
  have hπsquare : C (π ^ 2) ∈ p := by
    change ψ (C (π ^ 2)) ∈ IsLocalRing.maximalIdeal L
    rw [algHom_C, map_pow, pow_two]
    exact (IsLocalRing.maximalIdeal L).mul_mem_right _ hπ
  have hf (j : m) : f j ∈ p := by
    have hzero : q (principalLiftingRelation π f j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ideal.span (Set.range (principalLiftingRelation π f)) ≤ J from
          le_sup_left) (Ideal.subset_span ⟨j, rfl⟩))
    have heq : φ (principalLiftingRelation π f j) = 0 := by
      change β (q (principalLiftingRelation π f j)) = 0
      rw [hzero, map_zero]
    rw [principalLiftingRelation, map_sub, map_mul, algHom_C, sub_eq_zero] at heq
    change ψ (f j) = algebraMap R L π * φ (X (Sum.inr j)) at heq
    change ψ (f j) ∈ IsLocalRing.maximalIdeal L
    rw [heq]
    exact (IsLocalRing.maximalIdeal L).mul_mem_right _ hπ
  have houtside : A t ∉ p :=
    IsLocalRing.notMem_maximalIdeal.mpr (show IsUnit (ψ (A t)) from hA)
  obtain ⟨b, hb, hdet⟩ := exists_original_jacobianMinor_notMem_of_principal_quotient
    π P f hP a (A t) p hπsquare hf houtside hminor
  have hminorUnit : IsUnit (β (q (rename Sum.inl
      (Matrix.of (fun j i => pderiv (b i) (f (a j)))).det))) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    exact hdet
  exact exists_smooth_localization_of_principalLifting_selected_minor π hstable P f hP
    A H g hrel t a ha hdiag hsupport hzero hminor b hb β hA hminorUnit

/-- The full lifting algebra is smooth at every prime containing the base
parameter and avoiding the selected strictly-standard parameter. -/
theorem isSmoothAt_principalLifting_of_strictStandard
    {R n m k κ : Type*} [CommRing R] [Finite k]
    [Finite n] [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]
    (π : R) (hstable : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    {B : Type*} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hP : ∀ j, P.relation j = map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j))
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ i, H s j i * f i + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hzero : ∀ i, g t (a i) = 0)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det)) :
    let D := MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f A H g
    ∀ p : PrimeSpectrum D, algebraMap R D π ∈ p.asIdeal →
      Ideal.Quotient.mk _ (rename Sum.inl (A t)) ∉ p.asIdeal → IsSmoothAt R p.asIdeal := by
  intro D p hπ hA
  let L := Localization.AtPrime p.asIdeal
  let β : D →ₐ[R] L := IsScalarTower.toAlgHom R D L
  have hfg : (principalLiftingIdeal π f A H g).FG :=
    (Submodule.fg_span (Set.finite_range _)).sup
      (Submodule.fg_span (Set.finite_range _))
  have : FinitePresentation R D := FinitePresentation.quotient hfg
  have hπL : algebraMap R L π ∈ IsLocalRing.maximalIdeal L := by
    rw [IsScalarTower.algebraMap_apply R D L]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L p.asIdeal _).mpr hπ
  have hAL : IsUnit (β (Ideal.Quotient.mk _ (rename Sum.inl (A t)))) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff L p.asIdeal _).mpr hA
  obtain ⟨d, hd, hunit, _⟩ :=
    exists_smooth_localization_of_principalLifting_strictStandard (R := R) (L := L)
      π hstable P f hP
      A H g hrel t a ha hdiag hsupport hzero hminor β hπL hAL
  have hdp : d ∉ p.asIdeal :=
    (IsLocalization.AtPrime.isUnit_to_map_iff L p.asIdeal d).mp hunit
  exact (basicOpen_subset_smoothLocus_iff_smooth (R := R)).mpr hd
    ((PrimeSpectrum.mem_basicOpen d p).mpr hdp)

end Algebra
