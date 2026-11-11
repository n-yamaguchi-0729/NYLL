/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Translation of polynomial presentations

Translating each coordinate by a specified base-ring element gives an actual
algebra automorphism and an equivalence of the original and translated
quotients. Constant terms become evaluation at the specified point, and
partial derivatives commute with translation. The transported target map
has the original coordinate values minus the specified point.
-/

@[expose] public section

noncomputable section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommRing R] (a : σ → R)

/-- Translation by a base-ring point, with the actual inverse translation. -/
def coordinateTranslation : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i + C (a i)))
    (aeval (fun i => X i - C (a i)))
    (by
      apply algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, map_sub, aeval_C, algebraMap_eq,
        AlgHom.id_apply, add_sub_cancel_right])
    (by
      apply algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, map_add, aeval_C, algebraMap_eq,
        AlgHom.id_apply, sub_add_cancel])

theorem coordinateTranslation_apply (p : MvPolynomial σ R) :
    coordinateTranslation a p = aeval (fun i => X i + C (a i)) p :=
  rfl

theorem coordinateTranslation_symm_apply (p : MvPolynomial σ R) :
    (coordinateTranslation a).symm p = aeval (fun i => X i - C (a i)) p :=
  rfl

@[simp]
theorem coordinateTranslation_X (i : σ) :
    coordinateTranslation a (X i) = X i + C (a i) :=
  aeval_X _ _

@[simp]
theorem coordinateTranslation_symm_X (i : σ) :
    (coordinateTranslation a).symm (X i) = X i - C (a i) :=
  aeval_X _ _

@[simp]
theorem coordinateTranslation_C (r : R) :
    coordinateTranslation a (C r) = C r :=
  (coordinateTranslation a).commutes r

/-- Evaluation after translation is evaluation at the translated point. -/
theorem aeval_coordinateTranslation {S : Type w} [CommRing S] [Algebra R S]
    (b : σ → S) (p : MvPolynomial σ R) :
    aeval b (coordinateTranslation a p) =
      aeval (fun i => b i + algebraMap R S (a i)) p := by
  rw [coordinateTranslation_apply, comp_aeval_apply]
  simp only [map_add, aeval_X, aeval_C]

/-- The translated constant term is the original value at the chosen point. -/
theorem constantCoeff_coordinateTranslation (p : MvPolynomial σ R) :
    constantCoeff (coordinateTranslation a p) = aeval a p := by
  have h := aeval_coordinateTranslation a (fun _ : σ => (0 : R)) p
  simpa only [aeval_zero', Algebra.algebraMap_self_apply, zero_add] using h

/-- Coordinate translation commutes with every partial derivative. -/
theorem pderiv_coordinateTranslation (i : σ) (p : MvPolynomial σ R) :
    pderiv i (coordinateTranslation a p) = coordinateTranslation a (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp only [coordinateTranslation_C, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    obtain rfl | hji := eq_or_ne j i
    · simp only [map_mul, coordinateTranslation_X, pderiv_mul, map_add,
        pderiv_X_self, pderiv_C, hp, add_zero, mul_one]
    · simp only [map_mul, coordinateTranslation_X, pderiv_mul, map_add,
        pderiv_X_of_ne hji, pderiv_C, hp, add_zero, mul_zero]

/-- The Jacobian at the specified point is the constant Jacobian after translation. -/
theorem constantCoeff_pderiv_coordinateTranslation (i : σ) (p : MvPolynomial σ R) :
    constantCoeff (pderiv i (coordinateTranslation a p)) = aeval a (pderiv i p) := by
  rw [pderiv_coordinateTranslation, constantCoeff_coordinateTranslation]

/-- Translation takes a relation ideal to the ideal of the translated relations. -/
theorem coordinateTranslation_map_span {ι : Type*} (f : ι → MvPolynomial σ R) :
    Ideal.map (coordinateTranslation a).toAlgHom.toRingHom (Ideal.span (Set.range f)) =
      Ideal.span (Set.range (fun i => coordinateTranslation a (f i))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- The original quotient is equivalent to the quotient by its translated ideal. -/
def coordinateTranslationQuotientEquiv (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) ≃ₐ[R]
      MvPolynomial σ R ⧸ I.map (coordinateTranslation a).toAlgHom.toRingHom :=
  Ideal.quotientEquivAlg I _ (coordinateTranslation a) rfl

theorem coordinateTranslationQuotientEquiv_mk (I : Ideal (MvPolynomial σ R))
    (p : MvPolynomial σ R) :
    coordinateTranslationQuotientEquiv a I (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I.map (coordinateTranslation a).toAlgHom.toRingHom)
        (coordinateTranslation a p) :=
  rfl

theorem coordinateTranslationQuotientEquiv_symm_mk (I : Ideal (MvPolynomial σ R))
    (p : MvPolynomial σ R) :
    (coordinateTranslationQuotientEquiv a I).symm
        (Ideal.Quotient.mk (I.map (coordinateTranslation a).toAlgHom.toRingHom) p) =
      Ideal.Quotient.mk I ((coordinateTranslation a).symm p) :=
  rfl

variable {S : Type w} [CommRing S] [Algebra R S]

/-- The target map on the translated presentation, obtained from the actual quotient equivalence. -/
def translatedQuotientMap (I : Ideal (MvPolynomial σ R))
    (φ : (MvPolynomial σ R ⧸ I) →ₐ[R] S) :
    (MvPolynomial σ R ⧸ I.map (coordinateTranslation a).toAlgHom.toRingHom) →ₐ[R] S :=
  φ.comp (coordinateTranslationQuotientEquiv a I).symm.toAlgHom

/-- Its actual coordinate values are centered at the specified point. -/
theorem translatedQuotientMap_X (I : Ideal (MvPolynomial σ R))
    (φ : (MvPolynomial σ R ⧸ I) →ₐ[R] S) (i : σ) :
    translatedQuotientMap a I φ
        (Ideal.Quotient.mk (I.map (coordinateTranslation a).toAlgHom.toRingHom) (X i)) =
      φ (Ideal.Quotient.mk I (X i)) - algebraMap R S (a i) := by
  change φ (Ideal.Quotient.mk I ((coordinateTranslation a).symm (X i))) = _
  rw [coordinateTranslation_symm_X, map_sub, map_sub]
  congr 1
  exact φ.commutes (a i)

/-- The centered map recovers the exact original target map. -/
theorem translatedQuotientMap_comp (I : Ideal (MvPolynomial σ R))
    (φ : (MvPolynomial σ R ⧸ I) →ₐ[R] S) :
    (translatedQuotientMap a I φ).comp
      (coordinateTranslationQuotientEquiv a I).toAlgHom = φ := by
  apply AlgHom.ext
  intro x
  exact congrArg φ ((coordinateTranslationQuotientEquiv a I).symm_apply_apply x)

end MvPolynomial
