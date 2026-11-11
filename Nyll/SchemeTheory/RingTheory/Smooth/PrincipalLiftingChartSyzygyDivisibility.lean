/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.StrictStandardCoefficientCompatibility
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingSyzygyCross
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Divisibility of the remaining syzygies on a selected lifting chart

The original coefficient identities descend modulo the square of the
lifting parameter. Their actual strictly-standard compatibility lifts back
through the surjective coefficient map, with a remainder divisible by the
square. On the selected chart all these cross coefficients lie in the
parameter ideal. The exact polynomial cross identity then proves that
every remaining divided syzygy also lies in that ideal.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

open scoped BigOperators

/-- Lift actual selected-ideal membership through coefficient reduction
modulo a principal square. The extra term is in the square-parameter ideal. -/
theorem mem_selected_sup_principalSquare_of_map_mem
    {R n κ : Type*} [CommRing R] (π : R) (f : κ → MvPolynomial n R)
    (x : MvPolynomial n R)
    (hx : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) x ∈
      Ideal.span (Set.range fun i =>
        map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f i))) :
    x ∈ Ideal.span (Set.range f) ⊔ Ideal.span {C (π ^ 2)} := by
  let ρ : R →+* R ⧸ Ideal.span {π ^ 2} := Ideal.Quotient.mk (Ideal.span {π ^ 2})
  let μ : MvPolynomial n R →+* MvPolynomial n (R ⧸ Ideal.span {π ^ 2}) := map ρ
  have hsur : Function.Surjective μ := map_surjective ρ Ideal.Quotient.mk_surjective
  have hx' : μ x ∈ (Ideal.span (Set.range f)).map μ := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact hx
  obtain ⟨y, hy, heq⟩ := (Ideal.mem_map_iff_of_surjective μ hsur).mp hx'
  have hzero : map ρ (x - y) = 0 := by
    change μ (x - y) = 0
    rw [map_sub, heq, sub_self]
  have hdiv : C (π ^ 2) ∣ x - y := by
    apply (C_dvd_iff_map_hom_eq_zero ρ (π ^ 2) (fun r => ?_) _).mpr hzero
    change Ideal.Quotient.mk (Ideal.span {π ^ 2}) r = 0 ↔ π ^ 2 ∣ r
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hrem : x - y ∈ Ideal.span {C (π ^ 2)} := Ideal.mem_span_singleton.mpr hdiv
  have hsum : y + (x - y) ∈ Ideal.span (Set.range f) ⊔ Ideal.span {C (π ^ 2)} :=
    (Ideal.span (Set.range f) ⊔ Ideal.span {C (π ^ 2)}).add_mem
      ((show Ideal.span (Set.range f) ≤
        Ideal.span (Set.range f) ⊔ Ideal.span {C (π ^ 2)} from le_sup_left) hy)
      ((show Ideal.span {C (π ^ 2)} ≤
        Ideal.span (Set.range f) ⊔ Ideal.span {C (π ^ 2)} from le_sup_right) hrem)
  convert hsum using 1
  ring

/-- The actual lifted coefficient systems have the required cross-ideal
membership before reduction. It is derived from the original presentation
modulo the parameter square and coefficient-map surjectivity. -/
theorem sq_mul_crossCoefficient_mem_selected_sup_principalSquare
    {R n m k κ : Type*} [CommRing R] [Finite n] [Fintype m]
    [Fintype κ] [DecidableEq κ] (π : R)
    {B : Type*} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Algebra.Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hP : ∀ j, P.relation j = map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j))
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ l, H s j l * f l + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det)) :
    ∀ s j l, (A t) ^ 2 * (A s * H t j l - ∑ r, H s j r * H t r l) ∈
      Ideal.span (Set.range fun i => f (a i)) ⊔ Ideal.span {C (π ^ 2)} := by
  classical
  let ρ : R →+* R ⧸ Ideal.span {π ^ 2} := Ideal.Quotient.mk (Ideal.span {π ^ 2})
  let μ : MvPolynomial n R →+* MvPolynomial n (R ⧸ Ideal.span {π ^ 2}) := map ρ
  have hπ : ρ (π ^ 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have hC : μ (C (π ^ 2)) = 0 := by
    change map ρ (C (π ^ 2)) = 0
    rw [map_C, hπ, map_zero]
  have hbar (s : k) (j : m) :
      μ (A s) * P.relation j = ∑ l, μ (H s j l) * P.relation l := by
    have heq := congrArg μ (hrel s j)
    simp only [map_mul, map_add, map_sum, hC, zero_mul, add_zero] at heq
    simpa only [hP] using heq
  have htarget (j : m) :
      μ (A t) * P.relation j = ∑ i, μ (H t j (a i)) * P.relation (a i) := by
    rw [hbar t j]
    symm
    apply Fintype.sum_of_injective a ha
    · intro l hl
      rw [hsupport j l hl, map_zero, zero_mul]
    · intro i
      rfl
  intro s j l
  by_cases hl : l ∈ Set.range a
  · obtain ⟨i, rfl⟩ := hl
    have hbarCross := P.sq_mul_crossCoefficient_mem_selected a (μ (A s)) (μ (A t))
      hminor (fun j l => μ (H s j l)) (fun j i => μ (H t j (a i)))
      (hbar s) htarget j i
    apply mem_selected_sup_principalSquare_of_map_mem π (fun i => f (a i))
    simpa only [map_pow, map_mul, map_sub, map_sum, hP] using hbarCross
  · have hz (r : m) : H t r l = 0 := hsupport r l hl
    have heq : (A t) ^ 2 * (A s * H t j l - ∑ r, H s j r * H t r l) = 0 := by
      simp only [hz, mul_zero, Finset.sum_const_zero, sub_self]
    rw [heq]
    exact (Ideal.span (Set.range fun i => f (a i)) ⊔ Ideal.span {C (π ^ 2)}).zero_mem

/-- Every divided syzygy belongs to the parameter ideal on an actual
selected chart. The original lifting equations and chosen syzygies vanish
there, and the chosen parameter is a unit. Cross-coefficient compatibility
is proved from the presentation and is not an additional assumption. -/
theorem principalLiftingSyzygy_mem_parameterIdeal_of_selected_chart
    {R n m k κ D : Type*} [CommRing R] [Finite n] [Fintype m]
    [Fintype κ] [DecidableEq κ] [CommRing D] [Algebra R D] (π : R)
    {B : Type*} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Algebra.Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hP : ∀ j, P.relation j = map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j))
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ l, H s j l * f l + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det))
    (φ : MvPolynomial (n ⊕ m) R →ₐ[R] D)
    (hf : ∀ j, φ (principalLiftingRelation π f j) = 0)
    (ht : ∀ j, φ (principalLiftingSyzygy π A H g t j) = 0)
    (hA : IsUnit (φ (rename Sum.inl (A t)))) :
    ∀ s j, φ (principalLiftingSyzygy π A H g s j) ∈ Ideal.span {algebraMap R D π} := by
  let J : Ideal D := Ideal.span {algebraMap R D π}
  let ψ : MvPolynomial n R →ₐ[R] D := φ.comp (rename Sum.inl)
  have hπ : algebraMap R D π ∈ J := Ideal.subset_span (Set.mem_singleton _)
  have hselected (i : κ) : ψ (f (a i)) ∈ J := by
    have heq := hf (a i)
    rw [principalLiftingRelation, map_sub, map_mul, algHom_C, sub_eq_zero] at heq
    change ψ (f (a i)) = algebraMap R D π * φ (X (Sum.inr (a i))) at heq
    rw [heq]
    exact J.mul_mem_right _ hπ
  have hmap : (Ideal.span (Set.range fun i => f (a i)) ⊔
      Ideal.span {C (π ^ 2)}).map ψ.toRingHom ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hselected i
    · apply Ideal.span_le.mpr
      rintro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change ψ (C (π ^ 2)) ∈ J
      rw [algHom_C, map_pow, pow_two]
      exact J.mul_mem_left _ hπ
  have hcoeff (s : k) (j l : m) :
      ψ (A s * H t j l - ∑ r, H s j r * H t r l) ∈ J := by
    apply (Ideal.unit_mul_mem_iff_mem J (show IsUnit (ψ (A t) ^ 2) from hA.pow 2)).mp
    have hm := hmap (Ideal.mem_map_of_mem ψ.toRingHom
      (sq_mul_crossCoefficient_mem_selected_sup_principalSquare π P f hP A H g hrel
        t a ha hsupport hminor s j l))
    change ψ ((A t) ^ 2 * (A s * H t j l - ∑ r, H s j r * H t r l)) ∈ J at hm
    simpa only [map_mul, map_pow] using hm
  intro s j
  apply (Ideal.unit_mul_mem_iff_mem J hA).mp
  have heq := congrArg φ (principalLiftingSyzygy_cross π A H g s t j)
  simp only [map_add φ, map_sub φ, map_mul φ, map_sum φ, ht, mul_zero,
    Finset.sum_const_zero, sub_zero, add_zero, algHom_C] at heq
  rw [heq]
  exact J.add_mem
    (J.sum_mem fun l _ => J.mul_mem_right _ (hcoeff s j l))
    (J.mul_mem_right _ hπ)

end MvPolynomial
