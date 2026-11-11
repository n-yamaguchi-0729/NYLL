/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.MvPolynomialQuotientSection
public import Nyll.SchemeTheory.RingTheory.Smooth.StrictStandardPresentationBaseChange
public import Nyll.SchemeTheory.RingTheory.Smooth.ResidualQuotientSmoothAtFlatPrime
public import Nyll.SchemeTheory.RingTheory.Smooth.AlgebraIsSmoothAtFlatLocalizationAtPrime

/-!
# A uniform correction power before choosing the intermediate algebra

The two original Noetherian rings determine the power before the finite-type
intermediate algebra is chosen. A compatible quotient map constructs an actual
residual quotient, relatively smooth above the intermediate algebra's flat
locus and smooth over the original base above its smooth locus. When the
intermediate algebra is smooth, the residual quotient is smooth globally.
-/

@[expose] public section

noncomputable section

universe u

namespace Algebra

open MvPolynomial

/-- Smoothness at a prime composes through the actual localization at its
contracted prime. The localized algebra and its scalar towers are native. -/
theorem IsSmoothAt.comp
    {R D A : Type*} [CommRing R] [CommRing D] [CommRing A]
    [Algebra R D] [Algebra D A] [Algebra R A] [IsScalarTower R D A]
    (q : Ideal A) [q.IsPrime]
    [IsSmoothAt R (q.comap (algebraMap D A))] [IsSmoothAt D q] :
    IsSmoothAt R q := by
  let p : Ideal D := q.comap (algebraMap D A)
  have : q.LiesOver p := ⟨rfl⟩
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q) :=
    FormallySmooth.of_restrictScalars D (Localization.AtPrime p) (Localization.AtPrime q)
  exact FormallySmooth.comp R (Localization.AtPrime p) (Localization.AtPrime q)

/-- The exponent is chosen from the original base and target before any
intermediate finite-type algebra is supplied. A compatible quotient map then
constructs a residual quotient that is smooth over the intermediate algebra
at every prime above its original-base flat locus, and smooth over the original
base above its smooth locus. -/
theorem exists_uniform_power_relative_residual_factorization
    {R L m n k : Type u}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [IsNoetherianRing L]
    [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (D : Type u) [CommRing D] [Algebra R D] [FiniteType R D]
        [Algebra D L] [IsScalarTower R D L]
        (ρ : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
          D ⧸ Ideal.span {(algebraMap R D (π ^ N)) ^ 4})
        (φ : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L),
        (Ideal.Quotient.mkₐ R
          ((Ideal.span {(algebraMap R D (π ^ N)) ^ 4}).map (algebraMap D L))).comp φ =
          ((Ideal.quotientMapₐ
            ((Ideal.span {(algebraMap R D (π ^ N)) ^ 4}).map (algebraMap D L))
            (Algebra.ofId D L) Ideal.le_comap_map).restrictScalars R).comp ρ →
      ∃ (E : Type u) (_ : CommRing E) (_ : Algebra D E) (_ : Algebra R E)
        (_ : IsScalarTower R D E), Smooth D E ∧ ∃ J : Ideal E,
          J.FG ∧ J ≤ Ideal.span {algebraMap R E (π ^ N) ^ 2} ∧
          Ideal.span {algebraMap R E (π ^ N)} * J ≤ J ^ 2 ∧
          FinitePresentation D (E ⧸ J) ∧ FinitePresentation R (E ⧸ J) ∧
          (∀ (q : Ideal (E ⧸ J)) [q.IsPrime],
            Module.Flat R (Localization.AtPrime (q.comap (algebraMap D (E ⧸ J)))) →
              IsSmoothAt D q) ∧
          (∀ (q : Ideal (E ⧸ J)) [q.IsPrime],
            IsSmoothAt R (q.comap (algebraMap D (E ⧸ J))) → IsSmoothAt R q) ∧
          ∃ (α : (MvPolynomial n R ⧸
              (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] E ⧸ J)
            (β : E ⧸ J →ₐ[D] L), (β.restrictScalars R).comp α = φ := by
  classical
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    ((eventually_annihilator_pow_stable π).and
      (eventually_annihilator_pow_stable (algebraMap R L π)))
  refine ⟨b + 1, Nat.zero_lt_succ b, ?_⟩
  intro D _ _ _ _ _ ρ φ hcompat
  have : IsNoetherianRing D := FiniteType.isNoetherianRing R D
  let I : Ideal (MvPolynomial n R) :=
    Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)
  have hminorN : C (π ^ (b + 1)) ∈ I ⊔
      Ideal.span (Set.range fun c : m → n =>
        ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det) := by
    rw [map_pow, pow_succ]
    exact (I ⊔ _).mul_mem_left _ hminor
  have hrelationsN (j : k) : C (π ^ (b + 1)) * h j ∈
      Ideal.span (Set.range f) ⊔ I ^ 2 := by
    rw [map_pow, pow_succ (C π) b, mul_assoc]
    exact (Ideal.span (Set.range f) ⊔ I ^ 2).mul_mem_left _ (hrelations j)
  obtain ⟨hR, hL⟩ := hb (b + 1) (Nat.le_succ b)
  have hstableL : ∀ x : L,
      algebraMap D L (algebraMap R D (π ^ (b + 1))) ^ 2 * x = 0 →
        algebraMap D L (algebraMap R D (π ^ (b + 1))) * x = 0 := by
    simpa only [← IsScalarTower.algebraMap_apply R D L, map_pow] using hL
  have hπD : algebraMap D L (algebraMap R D (π ^ (b + 1))) ∈
      IsLocalRing.maximalIdeal L := by
    rw [← IsScalarTower.algebraMap_apply R D L, map_pow, pow_succ]
    exact (IsLocalRing.maximalIdeal L).mul_mem_left _ hπ
  obtain ⟨hminorD, hrelationsD⟩ := strictStandard_data_baseChange
    (S := D) (π ^ (b + 1)) f h hminorN hrelationsN
  obtain ⟨φD, hφD⟩ := exists_relationBaseChangeMap_lift (S := D) f h φ
  obtain ⟨ρD, hρD⟩ := exists_relationBaseChangeMap_lift (S := D) f h ρ
  let K : Ideal D := Ideal.span {(algebraMap R D (π ^ (b + 1))) ^ 4}
  let J : Ideal L := K.map (algebraMap D L)
  let qD : D ⧸ K →ₐ[D] L ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId D L) Ideal.le_comap_map
  have hcompatD : (Ideal.Quotient.mkₐ D J).comp φD = qD.comp ρD := by
    apply relationBaseChangeMap_hom_ext (R := R) f h
    apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk J (φD (relationBaseChangeMap (S := D) f h x)) =
      qD (ρD (relationBaseChangeMap (S := D) f h x))
    rw [show φD (relationBaseChangeMap (S := D) f h x) = φ x from
      AlgHom.congr_fun hφD x]
    rw [show ρD (relationBaseChangeMap (S := D) f h x) = ρ x from
      AlgHom.congr_fun hρD x]
    exact AlgHom.congr_fun hcompat x
  obtain ⟨E, _, _, hE, Kres, hKfg, hK, hrelK, αD, β, hβα⟩ :=
    exists_residual_quotient_factorization_of_quotient_section
      (algebraMap R D (π ^ (b + 1)))
      (fun j => map (algebraMap R D) (f j)) (fun j => map (algebraMap R D) (h j))
      hminorD hrelationsD hπD hstableL ρD φD hcompatD
  let _ : Algebra R E := ((algebraMap D E).comp (algebraMap R D)).toAlgebra
  have : IsScalarTower R D E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Smooth D E := hE
  have : FiniteType R E := FiniteType.trans
    (inferInstance : FiniteType R D) (inferInstance : FiniteType D E)
  have hfpD : FinitePresentation D (E ⧸ Kres) :=
    FinitePresentation.of_finiteType.mp inferInstance
  have hfpR : FinitePresentation R (E ⧸ Kres) :=
    FinitePresentation.of_finiteType.mp inferInstance
  have hK' : Kres ≤ Ideal.span {algebraMap R E (π ^ (b + 1)) ^ 2} := by
    simpa only [← IsScalarTower.algebraMap_apply R D E] using hK
  have hrelK' : Ideal.span {algebraMap R E (π ^ (b + 1))} * Kres ≤ Kres ^ 2 := by
    simpa only [← IsScalarTower.algebraMap_apply R D E] using hrelK
  have hlocal (q : Ideal (E ⧸ Kres)) [q.IsPrime]
      (hflat : Module.Flat R
        (Localization.AtPrime (q.comap (algebraMap D (E ⧸ Kres))))) : IsSmoothAt D q := by
    have : Module.Flat R
        (Localization.AtPrime (q.comap (algebraMap D (E ⧸ Kres)))) := hflat
    exact isSmoothAt_residualQuotient_of_flat_atPrime
      (π ^ (b + 1)) hR Kres hK' hrelK' q
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    hE, Kres, hKfg, hK', hrelK', hfpD, hfpR, hlocal, ?_,
    (αD.restrictScalars R).comp (relationBaseChangeMap (S := D) f h), β, ?_⟩
  · intro q _ hsm
    have : IsSmoothAt R (q.comap (algebraMap D (E ⧸ Kres))) := hsm
    have : FinitePresentation R D := FinitePresentation.of_finiteType.mp inferInstance
    have : Module.Flat R
        (Localization.AtPrime (q.comap (algebraMap D (E ⧸ Kres)))) :=
      IsSmoothAt.flat_localization_atPrime R D _
    have : IsSmoothAt D q := hlocal q inferInstance
    exact IsSmoothAt.comp (D := D) q
  · apply AlgHom.ext
    intro x
    change β (αD (relationBaseChangeMap (S := D) f h x)) = φ x
    rw [show β (αD (relationBaseChangeMap (S := D) f h x)) =
        φD (relationBaseChangeMap (S := D) f h x) from
      AlgHom.congr_fun hβα (relationBaseChangeMap (S := D) f h x)]
    exact AlgHom.congr_fun hφD x

/-- The power depends only on the original base and target, before the
intermediate smooth algebra and its compatible quotient map are chosen. -/
theorem exists_uniform_power_relative_smooth_factorization
    {R L m n k : Type u}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [IsNoetherianRing L]
    [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (D : Type u) [CommRing D] [Algebra R D] [Smooth R D]
        [Algebra D L] [IsScalarTower R D L]
        (ρ : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
          D ⧸ Ideal.span {(algebraMap R D (π ^ N)) ^ 4})
        (φ : (MvPolynomial n R ⧸
            (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L),
        (Ideal.Quotient.mkₐ R
          ((Ideal.span {(algebraMap R D (π ^ N)) ^ 4}).map (algebraMap D L))).comp φ =
          ((Ideal.quotientMapₐ
            ((Ideal.span {(algebraMap R D (π ^ N)) ^ 4}).map (algebraMap D L))
            (Algebra.ofId D L) Ideal.le_comap_map).restrictScalars R).comp ρ →
      ∃ (E : Type u) (_ : CommRing E) (_ : Algebra D E) (_ : Algebra R E)
        (_ : IsScalarTower R D E), Smooth D E ∧ Smooth R E ∧
          ∃ (α : (MvPolynomial n R ⧸
              (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] E)
            (β : E →ₐ[D] L), (β.restrictScalars R).comp α = φ := by
  obtain ⟨N, hpos, hN⟩ := exists_uniform_power_relative_residual_factorization
    (L := L) π f h hminor hrelations hπ
  refine ⟨N, hpos, ?_⟩
  intro D _ _ _ _ _ ρ φ hcompat
  obtain ⟨E, _, _, _, _, _hE, J, _hJfg, _hJ, _hrel, hfpD, _hfpR,
      hlocal, _habsolute, α, β, hβα⟩ := hN D ρ φ hcompat
  have : FinitePresentation D (E ⧸ J) := hfpD
  have hall : smoothLocus D (E ⧸ J) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    have : Module.Flat R
        (Localization.AtPrime (q.asIdeal.comap (algebraMap D (E ⧸ J)))) :=
      Module.Flat.trans R D _
    exact hlocal q.asIdeal inferInstance
  have : Smooth D (E ⧸ J) := ⟨smoothLocus_eq_univ_iff.mp hall, hfpD⟩
  have : Smooth R (E ⧸ J) := Smooth.comp R D (E ⧸ J)
  exact ⟨E ⧸ J, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, α, β, hβα⟩

end Algebra
