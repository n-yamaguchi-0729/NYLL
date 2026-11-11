/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingChartSmooth
public import Nyll.SchemeTheory.RingTheory.Smooth.ResidualRelationFactorization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Comparing a flat principal lifting chart with the full lifting algebra

The original base annihilator bound kills a parameter-divisible element
annihilated by the parameter in any flat algebra. Apply this to the actual
divided syzygies, then construct inverse maps between the localized chart
and full lifting quotients. The coordinate triangle is retained.
-/

@[expose] public section

noncomputable section

namespace Algebra

/-- In a flat algebra, the base bound `Ann(π²) = Ann(π)` kills every
element of `(π)` annihilated by `π`. -/
theorem eq_zero_of_mem_span_parameter_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (π : R) (hstable : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (x : S) (hx : x ∈ Ideal.span {algebraMap R S π})
    (hkill : algebraMap R S π * x = 0) : x = 0 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  have hyzero : algebraMap R S π ^ 2 * y = 0 := by
    rw [hy, ← mul_assoc, ← pow_two] at hkill
    exact hkill
  have hcontrol (z : R) (hz : π ^ 2 * z = 0) : 1 * π * z = 0 := by
    rw [one_mul]
    exact hstable z hz
  have hykill := annihilator_control_of_flat π 1 hcontrol y hyzero
  rw [map_one, one_mul] at hykill
  exact hy.trans hykill

end Algebra

namespace MvPolynomial

/-- Every actual selected chart equation is one of the full lifting
equations, after inserting the zero complementary coefficient columns. -/
theorem principalLiftingChartIdeal_le
    {R n m k κ : Type*} [CommRing R] [Fintype m] [Fintype κ]
    (π : R) (f : m → MvPolynomial n R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0) :
    Ideal.span (Set.range (principalLiftingChartRelations π f a (A t)
      (fun l i => H t l.val (a i)) (fun l => g t l.val))) ≤
        principalLiftingIdeal π f A H g := by
  let G := principalLiftingChartRelations π f a (A t)
    (fun l i => H t l.val (a i)) (fun l => g t l.val)
  have hsum (j : m) :
      (∑ l, rename (Sum.inl : n → n ⊕ m) (H t j l) * X (Sum.inr l)) =
        ∑ i, rename Sum.inl (H t j (a i)) * X (Sum.inr (a i)) := by
    symm
    apply Fintype.sum_of_injective a ha
    · intro l hl
      rw [hsupport j l hl, map_zero, zero_mul]
    · intro i
      rfl
  apply Ideal.span_le.mpr
  rintro _ ⟨u, rfl⟩
  cases u with
  | inl i =>
    exact (show Ideal.span (Set.range (principalLiftingRelation π f)) ≤
      principalLiftingIdeal π f A H g from le_sup_left)
        (Ideal.subset_span ⟨a i, rfl⟩)
  | inr l =>
    change G (Sum.inr l) ∈ principalLiftingIdeal π f A H g
    have hG : G (Sum.inr l) = principalLiftingSyzygy π A H g t l.val := by
      unfold principalLiftingSyzygy
      rw [hsum]
      rfl
    rw [hG]
    exact (show Ideal.span (Set.range (fun p : k × m =>
      principalLiftingSyzygy π A H g p.1 p.2)) ≤
        principalLiftingIdeal π f A H g from le_sup_right)
          (Ideal.subset_span ⟨(t, l.val), rfl⟩)


/-- Parameter-divisibility of the syzygies suffices in a flat algebra;
their vanishing follows from the original lifted relation identities. -/
theorem principalLiftingIdeal_le_ker_of_flat
    {R S n m k : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Fintype m]
    (π : R) (hstable : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (f : m → MvPolynomial n R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ i, H s j i * f i + C (π ^ 2) * g s j)
    (φ : MvPolynomial (n ⊕ m) R →ₐ[R] S)
    (hf : ∀ j, φ (principalLiftingRelation π f j) = 0)
    (hp : ∀ s j, φ (principalLiftingSyzygy π A H g s j) ∈
      Ideal.span {algebraMap R S π}) :
    principalLiftingIdeal π f A H g ≤ RingHom.ker φ.toRingHom := by
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hf j
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, j⟩, rfl⟩
    apply Algebra.eq_zero_of_mem_span_parameter_of_flat π hstable _ (hp s j)
    have heq := congrArg φ (mul_principalLiftingSyzygy π f A H g hrel s j)
    simpa only [map_mul, map_add, map_neg, map_sum, hf, mul_zero, neg_mul,
      Finset.sum_const_zero, zero_add, neg_zero, algHom_C] using heq

private theorem exists_localization_quotient_equiv
    {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
    (I J : Ideal P) (hIJ : I ≤ J) (d : P)
    (hJ : ∀ p ∈ J, algebraMap (P ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I d)) (Ideal.Quotient.mk I p) = 0) :
    ∃ e : Localization.Away (Ideal.Quotient.mk I d) ≃ₐ[R]
        Localization.Away (Ideal.Quotient.mk J d),
      ∀ p : P, e (algebraMap (P ⧸ I) _ (Ideal.Quotient.mk I p)) =
        algebraMap (P ⧸ J) _ (Ideal.Quotient.mk J p) := by
  let Q := P ⧸ I
  let D := P ⧸ J
  let U := Localization.Away (Ideal.Quotient.mk I d)
  let V := Localization.Away (Ideal.Quotient.mk J d)
  let qI : P →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let qJ : P →ₐ[R] D := Ideal.Quotient.mkₐ R J
  let lI : Q →ₐ[R] U := IsScalarTower.toAlgHom R Q U
  let lJ : D →ₐ[R] V := IsScalarTower.toAlgHom R D V
  let a : Q →ₐ[R] D := Ideal.Quotient.liftₐ I qJ
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hp))
  let b : D →ₐ[R] U := Ideal.Quotient.liftₐ J (lI.comp qI) hJ
  have ha (p : P) : a (qI p) = qJ p := rfl
  have hb (p : P) : b (qJ p) = lI (qI p) := rfl
  have had : IsUnit ((lJ.comp a) (Ideal.Quotient.mk I d)) := by
    change IsUnit (lJ (a (qI d)))
    rw [ha]
    exact IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk J d)
  have hbd : IsUnit (b (Ideal.Quotient.mk J d)) := by
    change IsUnit (b (qJ d))
    rw [hb]
    exact IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I d)
  let e : U →ₐ[R] V := IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk I d) had
  let e' : V →ₐ[R] U := IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk J d) hbd
  have he (x : Q) : e (lI x) = lJ (a x) :=
    IsLocalization.Away.lift_eq (Ideal.Quotient.mk I d) had x
  have he' (x : D) : e' (lJ x) = b x :=
    IsLocalization.Away.lift_eq (Ideal.Quotient.mk J d) hbd x
  have hee' : e.comp e' = AlgHom.id R V := by
    apply IsLocalization.algHom_ext (.powers (Ideal.Quotient.mk J d))
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro p
    change e (e' (lJ (qJ p))) = lJ (qJ p)
    rw [he', hb, he, ha]
  have he'e : e'.comp e = AlgHom.id R U := by
    apply IsLocalization.algHom_ext (.powers (Ideal.Quotient.mk I d))
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro p
    change e' (e (lI (qI p))) = lI (qI p)
    rw [he, ha, he', hb]
  refine ⟨AlgEquiv.ofAlgHom e e' hee' he'e, ?_⟩
  intro p
  change e (lI (qI p)) = lJ (qJ p)
  rw [he, ha]

/-- The actual selected chart and full lifting algebra have equivalent
localizations once the constructed cross-syzygy memberships hold in the
flat chart. No vanishing or comparison map for the full ideal is assumed. -/
theorem exists_principalLifting_chart_localization_equiv
    {R n m k κ : Type*} [CommRing R] [Fintype m] [DecidableEq m] [Fintype κ]
    (π : R) (hstable : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (f : m → MvPolynomial n R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ i, H s j i * f i + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hzero : ∀ i, g t (a i) = 0) (d : MvPolynomial (n ⊕ m) R) :
    let I := Ideal.span (Set.range (principalLiftingChartRelations π f a (A t)
      (fun l i => H t l.val (a i)) (fun l => g t l.val)))
    let Q := MvPolynomial (n ⊕ m) R ⧸ I
    let S := Localization.Away (Ideal.Quotient.mk I d)
    Module.Flat R S →
      IsUnit (algebraMap Q S (Ideal.Quotient.mk I (rename Sum.inl (A t)))) →
      (∀ s j, algebraMap Q S (Ideal.Quotient.mk I
        (principalLiftingSyzygy π A H g s j)) ∈ Ideal.span {algebraMap R S π}) →
      ∃ e : S ≃ₐ[R] Localization.Away
          (Ideal.Quotient.mk (principalLiftingIdeal π f A H g) d),
        ∀ p, e (algebraMap Q S (Ideal.Quotient.mk I p)) =
          algebraMap (MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f A H g) _
            (Ideal.Quotient.mk (principalLiftingIdeal π f A H g) p) := by
  intro I Q S hflat hA hp
  let G := principalLiftingChartRelations π f a (A t)
    (fun l i => H t l.val (a i)) (fun l => g t l.val)
  let φ : MvPolynomial (n ⊕ m) R →ₐ[R] S :=
    (IsScalarTower.toAlgHom R Q S).comp (Ideal.Quotient.mkₐ R I)
  have hchart (u) : φ (G u) = 0 := by
    have hzero : Ideal.Quotient.mk I (G u) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨u, rfl⟩)
    change algebraMap Q S (Ideal.Quotient.mk I (G u)) = 0
    rw [hzero, map_zero]
  have hf := (principalLifting_equations_zero_of_chart π f A H g hrel t a ha
    hdiag hsupport hzero φ hchart hA).1
  have hker := principalLiftingIdeal_le_ker_of_flat π hstable f A H g hrel φ hf hp
  have hIJ : I ≤ principalLiftingIdeal π f A H g :=
    principalLiftingChartIdeal_le π f A H g t a ha hsupport
  exact exists_localization_quotient_equiv I (principalLiftingIdeal π f A H g) hIJ d
    (fun p hp => hker hp)

end MvPolynomial
