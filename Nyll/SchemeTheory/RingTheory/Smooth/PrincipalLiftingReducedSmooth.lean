/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingReducedPolynomial
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Algebra.Tower

/-!
# Relative smoothness of the reduced principal lifting chart

The original-variable inclusion constructs the canonical map between the
actual reduced relation and lifting algebras. Its polynomial triangle agrees
with the coefficient map in the reduced polynomial equivalence. This upgrades
that equivalence over the original reduced algebra and proves relative
smoothness on the entire chosen principal open.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

/-- The canonical reduced algebra map induced by the original variables.
The original lifted equations and the killed parameter supply its kernel. -/
def principalLiftingReductionMap
    {R n m k : Type*} [CommRing R] [Fintype m]
    (π : R) (f : m → MvPolynomial n R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R) :
    (MvPolynomial n R ⧸ (Ideal.span (Set.range f) ⊔ Ideal.span {C π})) →ₐ[R]
      (MvPolynomial (n ⊕ m) R ⧸
        (principalLiftingIdeal π f A H g ⊔ Ideal.span {C π})) := by
  let I₀ : Ideal (MvPolynomial n R) := Ideal.span (Set.range f) ⊔ Ideal.span {C π}
  let J₀ : Ideal (MvPolynomial (n ⊕ m) R) :=
    principalLiftingIdeal π f A H g ⊔ Ideal.span {C π}
  let q : MvPolynomial (n ⊕ m) R →ₐ[R] (MvPolynomial (n ⊕ m) R ⧸ J₀) :=
    Ideal.Quotient.mkₐ R J₀
  let ψ := q.comp (rename (R := R) (Sum.inl : n → n ⊕ m))
  have hπ : q (C π) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span {C π} ≤ J₀ from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _)))
  have hf (j : m) : ψ (f j) = 0 := by
    have hh : q (principalLiftingRelation π f j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ideal.span (Set.range (principalLiftingRelation π f)) ≤ J₀ from
          le_trans le_sup_left le_sup_left) (Ideal.subset_span ⟨j, rfl⟩))
    rw [principalLiftingRelation, map_sub, map_mul, hπ, zero_mul, sub_zero] at hh
    exact hh
  have hker : I₀ ≤ RingHom.ker ψ.toRingHom := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hf j
    · apply Ideal.span_le.mpr
      rintro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change q (rename Sum.inl (C π)) = 0
      rw [rename_C, hπ]
  exact Ideal.Quotient.liftₐ I₀ ψ (fun p hp => hker hp)

/-- The canonical reduction map retains every original polynomial. -/
theorem principalLiftingReductionMap_mk
    {R n m k : Type*} [CommRing R] [Fintype m]
    (π : R) (f : m → MvPolynomial n R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R)
    (p : MvPolynomial n R) :
    principalLiftingReductionMap π f A H g (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename Sum.inl p) := rfl

/-- The chosen reduced principal open is smooth over the original reduced
relation algebra with its canonical algebra structure. Every prime in this
open is therefore relatively smooth, without a chosen coefficient comparison. -/
theorem principalLifting_reduced_smooth_over_original
    {R n m k κ : Type*} [CommRing R] [Finite n] [Fintype m] [DecidableEq m]
    [Fintype κ] [DecidableEq κ] (π : R)
    {B : Type*} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Algebra.Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hP : ∀ j, P.relation j = map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j))
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ l, H s j l * f l + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det)) :
    let I₀ : Ideal (MvPolynomial n R) := Ideal.span (Set.range f) ⊔ Ideal.span {C π}
    let C₀ := MvPolynomial n R ⧸ I₀
    let J₀ : Ideal (MvPolynomial (n ⊕ m) R) :=
      principalLiftingIdeal π f A H g ⊔ Ideal.span {C π}
    let D₀ := MvPolynomial (n ⊕ m) R ⧸ J₀
    let ρ₀ : C₀ →ₐ[R] D₀ := principalLiftingReductionMap π f A H g
    let _ : Algebra C₀ D₀ := ρ₀.toRingHom.toAlgebra
    let S := Localization.Away (Ideal.Quotient.mk I₀ (A t))
    let E := Localization.Away (Ideal.Quotient.mk J₀ (rename Sum.inl (A t)))
    Nonempty (E ≃ₐ[C₀] MvPolynomial κ S) ∧ Algebra.Smooth C₀ E ∧
      ∀ (q : Ideal D₀) (_ : q.IsPrime),
        Ideal.Quotient.mk J₀ (rename Sum.inl (A t)) ∉ q → Algebra.IsSmoothAt C₀ q := by
  intro I₀ C₀ J₀ D₀ ρ₀ hC₀D₀ S E
  have : IsScalarTower R C₀ D₀ := IsScalarTower.of_algHom ρ₀
  obtain ⟨α, e, heα, hα, _⟩ := exists_principalLifting_reduced_polynomial_equiv
    π P f hP A H g hrel t a ha hdiag hsupport hminor
  have hcanonical (x : C₀) : α (algebraMap C₀ S x) = algebraMap C₀ E x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hα, IsScalarTower.algebraMap_apply C₀ D₀ E]
    change algebraMap D₀ E (Ideal.Quotient.mk J₀ (rename Sum.inl p)) =
      algebraMap D₀ E (ρ₀ (Ideal.Quotient.mk I₀ p))
    rw [principalLiftingReductionMap_mk]
  let e₀ : E ≃ₐ[C₀] MvPolynomial κ S :=
    { e.toRingEquiv with
      commutes' := fun x => by
        change e (algebraMap C₀ E x) = algebraMap C₀ (MvPolynomial κ S) x
        rw [← hcanonical, heα]
        rfl }
  have : Algebra.Smooth C₀ S :=
    Algebra.Smooth.of_isLocalization_Away (Ideal.Quotient.mk I₀ (A t))
  have : Algebra.Smooth S (MvPolynomial κ S) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth C₀ (MvPolynomial κ S) :=
    Algebra.Smooth.comp C₀ S (MvPolynomial κ S)
  have hsm : Algebra.Smooth C₀ E := Algebra.Smooth.of_equiv e₀.symm
  refine ⟨⟨e₀⟩, hsm, ?_⟩
  intro q hq hd
  let T := Localization.AtPrime q
  let d := Ideal.Quotient.mk J₀ (rename Sum.inl (A t))
  have hle : Submonoid.powers d ≤ q.primeCompl := by
    rintro x ⟨i, rfl⟩
    exact fun hx => hd (hq.mem_of_pow_mem i hx)
  let _ : Algebra E T := IsLocalization.localizationAlgebraOfSubmonoidLe
    E T (Submonoid.powers d) q.primeCompl hle
  have : IsScalarTower D₀ E T := IsLocalization.localization_isScalarTower_of_submonoid_le
    E T (Submonoid.powers d) q.primeCompl hle
  have : IsLocalization (q.primeCompl.map (algebraMap D₀ E)) T :=
    IsLocalization.isLocalization_of_submonoid_le E T (Submonoid.powers d) q.primeCompl hle
  have : IsScalarTower C₀ E T :=
    IsScalarTower.of_algebraMap_eq (R := C₀) (S := E) (A := T) (fun x => by
      rw [IsScalarTower.algebraMap_apply C₀ D₀ T x,
        IsScalarTower.algebraMap_apply C₀ D₀ E x,
        ← IsScalarTower.algebraMap_apply D₀ E T])
  have : Algebra.FormallySmooth E T :=
    Algebra.FormallySmooth.of_isLocalization (q.primeCompl.map (algebraMap D₀ E))
  exact Algebra.FormallySmooth.comp C₀ E T

end MvPolynomial
