/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Degree.AlgHomLaurentSeriesDegEqOne
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.Orders.TranscendentalOrdNeZero
import Nyll.AlgebraicCurves.Places.Orders.TameLaurentDeformation
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.Algebra.UniformRing

/-! # Actual Laurent identification of a degree-one place completion

The original uniformizer embedding is dense because its image contains the
rational functions in the Laurent parameter. Its equality of normalized
orders identifies the uniformities. Uniqueness of uniform completion then
gives an algebra equivalence preserving the original embedding and valuation.
No algebraic closure of the constant field is required.
-/

noncomputable section

open scoped WithZero Topology WithZeroTopology Uniformity RatFunc
open MonoidWithZeroHom UniformSpace

private theorem valued_uniformity_basis_surjective
    {A : Type*} [Field A] [Valued A ℤᵐ⁰]
    (hsurj : Function.Surjective (Valued.v : Valuation A ℤᵐ⁰)) :
    (𝓤 A).HasBasis (fun γ : ℤᵐ⁰ => γ ≠ 0)
      (fun γ => {p : A × A | Valued.v (p.2 - p.1) < γ}) := by
  refine (Valued.hasBasis_uniformity A ℤᵐ⁰).to_hasBasis ?_ ?_
  · intro γ _
    refine ⟨ValueGroup₀.embedding γ.val, (γ.isUnit.map ValueGroup₀.embedding).ne_zero, ?_⟩
    intro p hp
    exact ((Valued.v : Valuation A ℤᵐ⁰).restrict_lt_iff_lt_embedding).mpr hp
  · intro γ hγ
    obtain ⟨a, ha⟩ := hsurj γ
    have hne : Valued.v.restrict a ≠ 0 := by
      intro h
      apply hγ
      calc
        γ = Valued.v a := ha.symm
        _ = 0 := ((Valued.v : Valuation A ℤᵐ⁰).restrict_eq_zero_iff).mp h
    refine ⟨Units.mk0 (Valued.v.restrict a) hne, trivial, ?_⟩
    intro p hp
    change Valued.v.restrict (p.2 - p.1) < Valued.v.restrict a at hp
    exact ha ▸ ((Valued.v : Valuation A ℤᵐ⁰).restrict_lt_iff).mp hp

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem laurentEmbedding_valuation (v : Place K F)
    (i : F →ₐ[K] LaurentSeries K) (hi : ∀ x : F, (i x).order = v.ord x) (x : F) :
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (i x) = v.adicValuation x := by
  by_cases hx : x = 0
  · subst x
    rw [map_zero, map_zero, map_zero]
  have hix : i x ≠ 0 := (map_ne_zero_iff i i.injective).mpr hx
  have hlog := (LaurentSeries.orderPlace (K := K)).ord_eq_neg_log_of_valuationSubring_eq
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) rfl
    (LaurentSeries.valuation_single_zpow K 1) hix
  rw [LaurentSeries.orderPlace_ord, hi x] at hlog
  have hv : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (i x) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hix
  rw [v.adicValuation_eq_exp_neg_ord hx, ← WithZero.exp_log hv]
  congr 1
  omega

private theorem laurentEmbedding_dense (v : Place K F) (t : F) (ht : v.ord t = 1)
    (i : F →ₐ[K] LaurentSeries K)
    (hit : i t = HahnSeries.single (1 : ℤ) (1 : K)) : DenseRange i := by
  have htr : Transcendental K t := v.transcendental_of_ord_ne_zero (ht ▸ one_ne_zero)
  let R : IntermediateField K F := IntermediateField.adjoin K {t}
  let e : RatFunc K ≃ₐ[K] R := RatFunc.algEquivOfTranscendental t htr
  let j : RatFunc K →ₐ[K] F := R.val.comp e.toAlgHom
  have htower := IsScalarTower.of_algebraMap_eq
    (R := K) (S := Polynomial K) (A := LaurentSeries K) (fun a => by
      rw [Polynomial.algebraMap_hahnSeries_apply, Polynomial.algebraMap_apply,
        Polynomial.coe_C]
      rfl)
  let k : RatFunc K →ₐ[K] LaurentSeries K :=
    IsScalarTower.toAlgHom K (RatFunc K) (LaurentSeries K)
  have hj : i.comp j = k := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    change i ((e RatFunc.X : R) : F) = ((RatFunc.X : RatFunc K) : LaurentSeries K)
    rw [RatFunc.algEquivOfTranscendental_X, hit, RatFunc.coe_X]
  apply (LaurentSeries.coe_range_dense (K := K)).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨j x, AlgHom.congr_fun hj x⟩

/-- An order-preserving embedding which sends a source uniformizer to the
Laurent parameter extends to an actual equivalence of completed fields.
The extension agrees with the supplied embedding on every original field
element and preserves the normalized multiplicative valuation. -/
theorem exists_adicCompletion_algEquiv_laurentSeries_of_embedding
    (v : Place K F) (t : F) (ht : v.ord t = 1)
    (i : F →ₐ[K] LaurentSeries K)
    (hit : i t = HahnSeries.single (1 : ℤ) (1 : K))
    (hi : ∀ x : F, (i x).order = v.ord x) :
    ∃ E : v.adicCompletion ≃ₐ[K] LaurentSeries K,
      (∀ x : F, E (algebraMap F v.adicCompletion x) = i x) ∧
      Continuous E ∧ Continuous E.symm ∧
      ∀ x : v.adicCompletion,
        (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x := by
  let A := WithVal (v.heightOneSpectrum.valuation F)
  let f : A →+* LaurentSeries K :=
    i.toRingHom.comp (WithVal.equiv (v.heightOneSpectrum.valuation F)).toRingHom
  have hfval (a : A) : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (f a) =
      (Valued.v : Valuation A ℤᵐ⁰) a :=
    laurentEmbedding_valuation v i hi a.ofVal
  have hsurjA : Function.Surjective (Valued.v : Valuation A ℤᵐ⁰) := by
    intro γ
    obtain ⟨a, ha⟩ := v.heightOneSpectrum.valuation_surjective F γ
    exact ⟨WithVal.toVal _ a, ha⟩
  have hbA := valued_uniformity_basis_surjective hsurjA
  have hbL := valued_uniformity_basis_surjective (LaurentSeries.valuation_surjective K)
  have hf : IsUniformInducing f := by
    apply (hbA.isUniformInducing_iff hbL).mpr
    constructor <;> intro γ hγ <;> refine ⟨γ, hγ, ?_⟩ <;> intro a b hab
    · change Valued.v (f b - f a) < γ
      rw [← map_sub, hfval]
      exact hab
    · change Valued.v (f b - f a) < γ at hab
      rw [← map_sub, hfval] at hab
      exact hab
  have hd : DenseRange f := by
    apply (laurentEmbedding_dense v t ht i hit).mono
    rintro _ ⟨a, rfl⟩
    exact ⟨WithVal.toVal _ a, rfl⟩
  let pkg : AbstractCompletion A :=
    { space := LaurentSeries K
      coe := f
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hf
      dense := hd }
  let eU : UniformSpace.Completion A ≃ᵤ LaurentSeries K :=
    AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg pkg
  let eH : UniformSpace.Completion A →+* LaurentSeries K :=
    UniformSpace.Completion.extensionHom f hf.uniformContinuous.continuous
  have heH (x : UniformSpace.Completion A) : eU x = eH x := rfl
  let eR : UniformSpace.Completion A ≃+* LaurentSeries K :=
    { eU with
      map_mul' x y := (heH (x * y)).trans ((eH.map_mul x y).trans
        (congrArg₂ (· * ·) (heH x) (heH y)).symm)
      map_add' x y := (heH (x + y)).trans ((eH.map_add x y).trans
        (congrArg₂ (· + ·) (heH x) (heH y)).symm) }
  let ER : v.adicCompletion ≃+* LaurentSeries K :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv F v.heightOneSpectrum).trans eR
  have hER (x : F) : ER (algebraMap F v.adicCompletion x) = i x :=
    UniformSpace.Completion.extensionHom_coe f hf.uniformContinuous.continuous (WithVal.toVal _ x)
  let E : v.adicCompletion ≃ₐ[K] LaurentSeries K :=
    { ER with
      commutes' a := by
        change ER (algebraMap K v.adicCompletion a) = _
        rw [IsScalarTower.algebraMap_apply K F v.adicCompletion, hER, i.commutes] }
  have hEc : Continuous E := eU.continuous.comp
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion F
      v.heightOneSpectrum)
  have hEic : Continuous E.symm :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion F
      v.heightOneSpectrum).comp eU.symm.continuous
  refine ⟨E, hER, hEc, hEic, ?_⟩
  intro x
  refine (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F
    v.heightOneSpectrum).induction_on x ?_ ?_
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective
        (LaurentSeries.valuation_surjective K)).comp hEc)
      (Valued.continuous_valuation_of_surjective
        (v.heightOneSpectrum.valuedAdicCompletion_surjective F))
  · intro a
    change Valued.v (ER (algebraMap F v.adicCompletion a)) = _
    rw [hER]
    exact (laurentEmbedding_valuation v i hi a).trans
      (AlgebraicCurve.valued_algebraMap_adicCompletion v a).symm

/-- At a degree-one place, the actual completed local field is the Laurent
field over the constants, with the chosen uniformizer sent to the Laurent
parameter and all original normalized orders preserved. -/
theorem exists_adicCompletion_algEquiv_laurentSeries_of_deg_eq_one
    (v : Place K F) (hv : v.deg = 1) (t : F) (ht : v.ord t = 1) :
    ∃ E : v.adicCompletion ≃ₐ[K] LaurentSeries K,
      E (algebraMap F v.adicCompletion t) = HahnSeries.single (1 : ℤ) (1 : K) ∧
      (∀ x : F, (E (algebraMap F v.adicCompletion x)).order = v.ord x) ∧
      Continuous E ∧ Continuous E.symm ∧
      ∀ x : v.adicCompletion,
        (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x := by
  obtain ⟨i, hit, hi⟩ := v.exists_algHom_laurentSeries_of_deg_eq_one hv t ht
  obtain ⟨E, hE, hEc, hEic, hEval⟩ :=
    v.exists_adicCompletion_algEquiv_laurentSeries_of_embedding t ht i hit hi
  exact ⟨E, (hE t).trans hit, fun x => (congrArg HahnSeries.order (hE x)).trans (hi x),
    hEc, hEic, hEval⟩

end AlgebraicCurve.Place
