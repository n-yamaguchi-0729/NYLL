/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingChartComparison
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingChartSyzygyDivisibility
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# A smooth chart of the full principal lifting algebra

The selected original Jacobian gives a smooth partial chart. Inverting its
chosen parameter as well makes the cross-syzygy argument applicable. Flatness
then kills all omitted equations, and the actual localized-quotient comparison
transfers smoothness to the full lifting algebra, retaining its target map.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace Algebra

/-- A selected strictly-standard family and a target-unit original minor
produce a genuine smooth localization of the full lifting algebra. The chart
flatness and omitted-syzygy divisibility are proved, not additional inputs. -/
theorem exists_smooth_localization_of_principalLifting_selected_minor
    {R L n m k κ : Type*} [CommRing R] [CommRing L] [Algebra R L]
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
    (b : κ → n) (hb : Function.Injective b)
    (β : (MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f A H g) →ₐ[R] L)
    (hA : IsUnit (β (Ideal.Quotient.mk _ (rename Sum.inl (A t)))))
    (hminorUnit : IsUnit (β (Ideal.Quotient.mk _ (rename Sum.inl
      (Matrix.of (fun j i => pderiv (b i) (f (a j)))).det)))) :
    ∃ d : MvPolynomial (n ⊕ m) R ⧸ principalLiftingIdeal π f A H g,
      Smooth R (Localization.Away d) ∧ IsUnit (β d) ∧
        ∃ γ : Localization.Away d →ₐ[R] L,
          γ.comp (IsScalarTower.toAlgHom R _ (Localization.Away d)) = β := by
  let G := principalLiftingChartRelations π f a (A t)
    (fun l i => H t l.val (a i)) (fun l => g t l.val)
  let I := Ideal.span (Set.range G)
  let J := principalLiftingIdeal π f A H g
  let Q := MvPolynomial (n ⊕ m) R ⧸ I
  let D := MvPolynomial (n ⊕ m) R ⧸ J
  let qI : MvPolynomial (n ⊕ m) R →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let qJ : MvPolynomial (n ⊕ m) R →ₐ[R] D := Ideal.Quotient.mkₐ R J
  have hIJ : I ≤ J := principalLiftingChartIdeal_le π f A H g t a ha hsupport
  let v : Q →ₐ[R] D := Ideal.Quotient.liftₐ I qJ
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hp))
  let βQ : Q →ₐ[R] L := β.comp v
  have hβQ (p : MvPolynomial (n ⊕ m) R) : βQ (qI p) = β (qJ p) := rfl
  have hAQ : IsUnit (βQ (qI (rename Sum.inl (A t)))) := by
    rw [hβQ]
    exact hA
  have hminorQ : IsUnit (βQ (qI (rename Sum.inl
      (Matrix.of (fun j i => pderiv (b i) (f (a j)))).det))) := by
    rw [hβQ]
    exact hminorUnit
  obtain ⟨u, hu, γ, hγ⟩ :=
    exists_standardSmooth_localization_of_principalLiftingChart π f a b hb (A t)
      (fun l i => H t l.val (a i)) (fun l => g t l.val) βQ hAQ hminorQ
  obtain ⟨j, rfl⟩ := Ideal.Quotient.mk_surjective u
  let T := Localization.Away (Ideal.Quotient.mk I j)
  have : IsStandardSmooth R T := hu
  let pA : MvPolynomial (n ⊕ m) R := rename Sum.inl (A t)
  let d : MvPolynomial (n ⊕ m) R := pA * j
  let U := Localization.Away (algebraMap Q T (Ideal.Quotient.mk I pA))
  let S := Localization.Away (Ideal.Quotient.mk I d)
  have : Smooth T U :=
    Smooth.of_isLocalization_Away (algebraMap Q T (Ideal.Quotient.mk I pA))
  have : Smooth R U := Smooth.comp R T U
  have : IsLocalization.Away (Ideal.Quotient.mk I d) U := by
    change IsLocalization.Away (Ideal.Quotient.mk I (pA * j)) U
    rw [map_mul]
    exact IsLocalization.Away.mul T U (Ideal.Quotient.mk I j) (Ideal.Quotient.mk I pA)
  let eUS : U ≃ₐ[Q] S := IsLocalization.algEquiv (.powers (Ideal.Quotient.mk I d)) U S
  have : Smooth R S := Smooth.of_equiv (eUS.restrictScalars R)
  have hAS : IsUnit (algebraMap Q S (qI pA)) := by
    have hd : IsUnit (algebraMap Q S (Ideal.Quotient.mk I d)) :=
      IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I d)
    change IsUnit (algebraMap Q S (Ideal.Quotient.mk I (pA * j))) at hd
    have hd' : IsUnit (algebraMap Q S (Ideal.Quotient.mk I pA) *
        algebraMap Q S (Ideal.Quotient.mk I j)) := by
      simpa only [map_mul] using hd
    exact isUnit_of_mul_isUnit_left hd'
  let φ : MvPolynomial (n ⊕ m) R →ₐ[R] S :=
    (IsScalarTower.toAlgHom R Q S).comp qI
  have hchart (c) : φ (G c) = 0 := by
    have hc : qI (G c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨c, rfl⟩)
    change algebraMap Q S (qI (G c)) = 0
    rw [hc, map_zero]
  have heq := principalLifting_equations_zero_of_chart π f A H g hrel t a ha
    hdiag hsupport hzero φ hchart hAS
  have hp := principalLiftingSyzygy_mem_parameterIdeal_of_selected_chart π P f hP
    A H g hrel t a ha hsupport hminor φ heq.1 heq.2 hAS
  obtain ⟨e, _⟩ := exists_principalLifting_chart_localization_equiv π hstable
    f A H g hrel t a ha hdiag hsupport hzero d inferInstance hAS hp
  have hγj : γ (algebraMap Q T (qI j)) = βQ (qI j) :=
    congrArg (fun w : Q →ₐ[R] L => w (qI j)) hγ
  have hjL : IsUnit (βQ (qI j)) := by
    rw [← hγj]
    exact (IsLocalization.Away.algebraMap_isUnit
      (Ideal.Quotient.mk I j)).map γ.toMonoidHom
  have hdL : IsUnit (β (Ideal.Quotient.mk J d)) := by
    change IsUnit (β (qJ d))
    rw [← hβQ]
    change IsUnit (βQ (qI (pA * j)))
    rw [map_mul, map_mul]
    exact hAQ.mul hjL
  refine ⟨Ideal.Quotient.mk J d, Smooth.of_equiv e, hdL,
    IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk J d) hdL, ?_⟩
  apply AlgHom.ext
  intro x
  exact IsLocalization.Away.lift_eq (Ideal.Quotient.mk J d) hdL x

end Algebra
