/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual algebra in the principal lifting construction

The relations `f_j - π z_j` and the divided original syzygies define a
finite presentation. An approximate solution modulo `π²` supplies its
map to the original target using the target annihilator bound. Reduction
modulo `π` recovers the original relation algebra. The polynomial identity
`π p = -a (f - π z) + Σ h (f - π z)` is retained for localization.

This is the algebra construction in the Stacks Project lifting lemma:
https://stacks.math.columbia.edu/tag/07CP
The smooth-locus assertion requires additional arguments.
-/

@[expose] public section

noncomputable section

universe u v w t z

namespace MvPolynomial

variable {R : Type u} {n : Type v} {m : Type w} {k : Type t}
  [CommRing R] [Fintype m]

/-- The lifted original relation, with its own new variable. -/
def principalLiftingRelation (π : R) (f : m → MvPolynomial n R) (j : m) :
    MvPolynomial (n ⊕ m) R :=
  rename Sum.inl (f j) - C π * X (Sum.inr j)

/-- The original syzygy divided by the lifting parameter. -/
def principalLiftingSyzygy (π : R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (s : k) (j : m) : MvPolynomial (n ⊕ m) R :=
  rename Sum.inl (a s) * X (Sum.inr j) -
    ∑ i, rename Sum.inl (h s j i) * X (Sum.inr i) - C π * rename Sum.inl (g s j)

/-- The exact syzygy identity used to remove the extra equations after
inverting the lifting parameter. -/
theorem mul_principalLiftingSyzygy
    (π : R) (f : m → MvPolynomial n R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, a s * f j = ∑ i, h s j i * f i + C (π ^ 2) * g s j)
    (s : k) (j : m) :
    C π * principalLiftingSyzygy π a h g s j =
      -rename Sum.inl (a s) * principalLiftingRelation π f j +
        ∑ i, rename Sum.inl (h s j i) * principalLiftingRelation π f i := by
  have heq := congrArg (rename (R := R) (Sum.inl : n → n ⊕ m)) (hrel s j)
  simp only [map_mul, map_add, map_sum, rename_C] at heq
  have hsum : C π * (∑ i, rename Sum.inl (h s j i) * X (Sum.inr i)) =
      ∑ i, rename Sum.inl (h s j i) * (C π * X (Sum.inr i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold principalLiftingSyzygy principalLiftingRelation
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsum, neg_mul, heq, map_pow]
  ring

/-- The actual ideal of the principal lifting algebra. -/
def principalLiftingIdeal (π : R) (f : m → MvPolynomial n R)
    (a : k → MvPolynomial n R) (h : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R) : Ideal (MvPolynomial (n ⊕ m) R) :=
  Ideal.span (Set.range (principalLiftingRelation π f)) ⊔
    Ideal.span (Set.range (fun p : k × m => principalLiftingSyzygy π a h g p.1 p.2))

/-- An approximate solution kills the actual lifting ideal, including its
divided syzygies. The only cancellation used is the stated annihilator bound. -/
theorem principalLiftingIdeal_le_ker_aeval
    {L : Type z} [CommRing L] [Algebra R L]
    (π : R) (f : m → MvPolynomial n R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, a s * f j = ∑ i, h s j i * f i + C (π ^ 2) * g s j)
    (xval : n → L) (μ : m → L)
    (hf : ∀ j, aeval xval (f j) = algebraMap R L π ^ 2 * μ j)
    (hstable : ∀ x : L, algebraMap R L π ^ 2 * x = 0 →
      algebraMap R L π * x = 0) :
    principalLiftingIdeal π f a h g ≤
      RingHom.ker (aeval (Sum.elim xval (fun j => algebraMap R L π * μ j))).toRingHom := by
  let t := algebraMap R L π
  let v : n ⊕ m → L := Sum.elim xval (fun j => t * μ j)
  have hv (p : MvPolynomial n R) : aeval v (rename Sum.inl p) = aeval xval p :=
    aeval_rename Sum.inl v p
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change aeval v (principalLiftingRelation π f j) = 0
    rw [principalLiftingRelation, map_sub, hv, map_mul, aeval_C, aeval_X, hf]
    change t ^ 2 * μ j - t * (t * μ j) = 0
    ring
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, j⟩, rfl⟩
    change aeval v (principalLiftingSyzygy π a h g s j) = 0
    have heq := congrArg (aeval xval) (hrel s j)
    simp only [map_mul, map_add, map_sum, aeval_C, map_pow, hf] at heq
    let e : L := aeval xval (a s) * μ j -
      ∑ i, aeval xval (h s j i) * μ i - aeval xval (g s j)
    have hzero : t ^ 2 * e = 0 := by
      dsimp only [e]
      rw [mul_sub, mul_sub, Finset.mul_sum]
      have hsum : (∑ i, t ^ 2 * (aeval xval (h s j i) * μ i)) =
          ∑ i, aeval xval (h s j i) * (t ^ 2 * μ i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      change aeval xval (a s) * (t ^ 2 * μ j) =
        (∑ i, aeval xval (h s j i) * (t ^ 2 * μ i)) + t ^ 2 * aeval xval (g s j) at heq
      calc
        t ^ 2 * (aeval xval (a s) * μ j) -
            (∑ i, aeval xval (h s j i) * (t ^ 2 * μ i)) - t ^ 2 * aeval xval (g s j) =
          aeval xval (a s) * (t ^ 2 * μ j) -
            (∑ i, aeval xval (h s j i) * (t ^ 2 * μ i)) - t ^ 2 * aeval xval (g s j) := by ring
        _ = 0 := by rw [heq]; ring
    have he : t * e = 0 := hstable e hzero
    rw [principalLiftingSyzygy, map_sub, map_sub, map_mul, hv,
      aeval_X, map_sum, map_mul, aeval_C, hv]
    have hsum : (∑ i, aeval v (rename Sum.inl (h s j i) * X (Sum.inr i))) =
        t * ∑ i, aeval xval (h s j i) * μ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, hv, aeval_X]
      change aeval xval (h s j i) * (t * μ i) = t * (aeval xval (h s j i) * μ i)
      ring
    rw [hsum]
    change aeval xval (a s) * (t * μ j) -
      t * (∑ i, aeval xval (h s j i) * μ i) - t * aeval xval (g s j) = 0
    calc
      _ = t * e := by dsimp only [e]; ring
      _ = 0 := he

/-- The constructed finite presentation maps to the original target and
receives the original relation algebra after reduction modulo `π`. Both
maps retain the given polynomial coordinates. -/
theorem exists_principalLifting_algebra
    [Finite n] [Finite k]
    {L : Type z} [CommRing L] [Algebra R L]
    (π : R) (f : m → MvPolynomial n R) (a : k → MvPolynomial n R)
    (h : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, a s * f j = ∑ i, h s j i * f i + C (π ^ 2) * g s j)
    (xval : n → L) (μ : m → L)
    (hf : ∀ j, aeval xval (f j) = algebraMap R L π ^ 2 * μ j)
    (hstable : ∀ x : L, algebraMap R L π ^ 2 * x = 0 →
      algebraMap R L π * x = 0) :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : Algebra R D),
      Algebra.FinitePresentation R D ∧
        ∃ (θ : MvPolynomial (n ⊕ m) R →ₐ[R] D) (β : D →ₐ[R] L)
          (ρ : (MvPolynomial n R ⧸ Ideal.span (Set.range f)) →ₐ[R]
            D ⧸ Ideal.span {algebraMap R D π}),
          Function.Surjective θ ∧
          β.comp θ = aeval (Sum.elim xval (fun j => algebraMap R L π * μ j)) ∧
          ρ.comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) =
            (Ideal.Quotient.mkₐ R (Ideal.span {algebraMap R D π})).comp
              (θ.comp (rename Sum.inl)) := by
  let J := principalLiftingIdeal π f a h g
  let D := MvPolynomial (n ⊕ m) R ⧸ J
  let θ : MvPolynomial (n ⊕ m) R →ₐ[R] D := Ideal.Quotient.mkₐ R J
  have hJ : J.FG :=
    (Submodule.fg_span (Set.finite_range _)).sup
      (Submodule.fg_span (Set.finite_range _))
  have : Algebra.FinitePresentation R D := Algebra.FinitePresentation.quotient hJ
  let β : D →ₐ[R] L := Ideal.Quotient.liftₐ J
    (aeval (Sum.elim xval (fun j => algebraMap R L π * μ j)))
    (fun _ hx => principalLiftingIdeal_le_ker_aeval π f a h g hrel xval μ hf hstable hx)
  let q : D →ₐ[R] D ⧸ Ideal.span {algebraMap R D π} :=
    Ideal.Quotient.mkₐ R (Ideal.span {algebraMap R D π})
  let η := q.comp (θ.comp (rename (R := R) (Sum.inl : n → n ⊕ m)))
  have hπ : q (algebraMap R D π) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have hη : Ideal.span (Set.range f) ≤ RingHom.ker η.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hj : θ (principalLiftingRelation π f j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ideal.span (Set.range (principalLiftingRelation π f)) ≤ J from
          le_sup_left) (Ideal.subset_span ⟨j, rfl⟩))
    rw [principalLiftingRelation, map_sub, sub_eq_zero] at hj
    change q (θ (rename Sum.inl (f j))) = 0
    rw [hj, map_mul, map_mul]
    change q (algebraMap R D π) * q (θ (X (Sum.inr j))) = 0
    rw [hπ]
    exact MulZeroClass.zero_mul (q (θ (X (Sum.inr j))))
  let ρ := Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) η (fun _ hx => hη hx)
  exact ⟨D, inferInstance, inferInstance, inferInstance, θ, β, ρ,
    Ideal.Quotient.mkₐ_surjective R J, Ideal.Quotient.liftₐ_comp _ _ _,
    Ideal.Quotient.liftₐ_comp _ _ _⟩

end MvPolynomial
