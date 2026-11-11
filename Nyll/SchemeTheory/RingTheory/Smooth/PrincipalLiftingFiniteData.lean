/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.NoetherianSmoothLocusStrictStandardCover
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalRelationCoefficientLift

/-!
# A finite normalized lifting system from the original quotient presentation

The finite smooth-locus cover and exact selected-relation memberships supply
all the polynomial parameters, coefficient matrices and remainders of the
principal lifting construction. Diagonal normalization and column support
are constructed simultaneously for every member of the cover.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace Algebra

open MvPolynomial

/-- Construct a single finite full-index coefficient system whose quotient
parameters cover precisely the smooth locus of the original presentation. -/
theorem Presentation.exists_finite_normalized_principal_lifting_data
    {R : Type u} [CommRing R] (π : R)
    {B : Type v} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    [IsNoetherianRing B] {n : Type w} {m : Type t}
    [Finite n] [Fintype m] [DecidableEq m]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hf : ∀ j, map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) = P.relation j) :
    ∃ (s : Finset P.Ring) (A : s → MvPolynomial n R)
      (H : s → m → m → MvPolynomial n R) (g : s → m → MvPolynomial n R),
      (∀ t, map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) = t.val) ∧
      (∀ t j, A t * f j = ∑ l, H t j l * f l + C (π ^ 2) * g t j) ∧
      (∀ t, ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → m),
        Function.Injective a ∧
        (∀ i l, H t (a i) l = if l = a i then A t else 0) ∧
        (∀ j l, l ∉ Set.range a → H t j l = 0) ∧
        (∀ i, g t (a i) = 0) ∧
        t.val ∈ P.ker ⊔ Ideal.span (Set.range (fun b : κ → n =>
          ((Matrix.of fun j i => pderiv i (P.relation (a j))).submatrix _root_.id b).det))) ∧
      ∀ p : PrimeSpectrum B,
        p ∈ smoothLocus (R ⧸ Ideal.span {π ^ 2}) B ↔
          ∃ t : s, algebraMap P.Ring B t.val ∉ p.asIdeal := by
  classical
  obtain ⟨s, hs, hcover⟩ := P.exists_finite_strictStandard_cover_of_smoothLocus
  have hdata (t : s) :
      ∃ (A : MvPolynomial n R) (H : m → m → MvPolynomial n R)
        (g : m → MvPolynomial n R),
        map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) A = t.val ∧
        (∀ j, A * f j = ∑ l, H j l * f l + C (π ^ 2) * g j) ∧
        ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → m),
          Function.Injective a ∧
          (∀ i l, H (a i) l = if l = a i then A else 0) ∧
          (∀ j l, l ∉ Set.range a → H j l = 0) ∧
          (∀ i, g (a i) = 0) ∧
          t.val ∈ P.ker ⊔ Ideal.span (Set.range (fun b : κ → n =>
            ((Matrix.of fun j i => pderiv i (P.relation (a j))).submatrix _root_.id b).det)) := by
    obtain ⟨κ, hκ, hκdec, a, ha, hminor, hrelations⟩ := (hs t.val t.property).2
    let _ : Fintype κ := hκ
    let _ : DecidableEq κ := hκdec
    have hrelations' (j : m) :
        t.val * map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) ∈
          Ideal.span (Set.range fun i =>
            map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f (a i))) := by
      simpa only [hf] using hrelations j
    obtain ⟨A, H, g, hA, hrel, hdiag, hsupport, hzero⟩ :=
      exists_full_normalized_lift_principal_relation_coefficients π f a ha t.val hrelations'
    exact ⟨A, H, g, hA, hrel, κ, hκ, hκdec, a, ha, hdiag, hsupport, hzero, hminor⟩
  choose A H g hA hrel hselected using hdata
  refine ⟨s, A, H, g, hA, hrel, hselected, ?_⟩
  intro p
  rw [hcover]
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact ⟨⟨q, hq⟩, hqp⟩
  · rintro ⟨t, htp⟩
    exact ⟨t.val, t.property, htp⟩

end Algebra
