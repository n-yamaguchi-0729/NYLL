/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantDescent
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.RingTheory.Derivation.Basic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.ConstantExtension.ComapAlgebraMapEqConstantExtension
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.PrincipalConstantExtension
import Nyll.AlgebraicCurves.FunctionFields.Constants.DerivationConstantExtensionMapMem
import Nyll.AlgebraicCurves.Places.Orders.OrdNegTranscendental

/-!
# Divisor exists torsion descent of constant Field Extension
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_exists_torsion_descent_of_constantFieldExtension
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace TorsionDescentDeriv

open _root_.AlgebraicCurve.Divisor _root_.AlgebraicCurve.ConstantDescent

section DerivationExistence

open scoped IntermediateField
open KaehlerDifferential MvPolynomial

theorem exists_derivation_apply_eq_one (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    [CharZero K] (t : K') (ht : Transcendental K t) :
    ∃ δ : Derivation K K' K', δ t = 1 := by
  classical
  have hind : AlgebraicIndepOn K id ({t} : Set K') :=
    (algebraicIndependent_singleton_iff (R := K) (x := fun i : ({t} : Set K') => (id (i : K')))
      ⟨t, Set.mem_singleton t⟩).mpr ht
  obtain ⟨B, htB, hB⟩ := exists_isTranscendenceBasis_superset hind
  set L : IntermediateField K K' := IntermediateField.adjoin K (Set.range ((↑) : B → K')) with hL
  have : Algebra.IsAlgebraic L K' := hB.isAlgebraic_field
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  have : Algebra.IsSeparable L K' := inferInstance
  let R := MvPolynomial B K
  let e : FractionRing R ≃ₐ[K] L := hB.1.aevalEquivField
  let iRL : Algebra R L := (e.toAlgHom.toRingHom.comp (algebraMap R (FractionRing R))).toAlgebra
  let iRK' : Algebra R K' := ((algebraMap L K').comp (algebraMap R L)).toAlgebra
  have : IsScalarTower R L K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgL : ∀ p : R, algebraMap R L p = e (algebraMap R (FractionRing R) p) := fun _ => rfl
  have halgK' : ∀ p : R, algebraMap R K' p = ((e (algebraMap R (FractionRing R) p) : L) : K') :=
    fun _ => rfl
  have halgK'' : ∀ p : R, algebraMap R K' p = MvPolynomial.aeval ((↑) : B → K') p := by
    intro p
    rw [halgK', AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  have : IsScalarTower K R K' := IsScalarTower.of_algebraMap_eq fun k => by
    rw [halgK'', MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  have : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq fun k => by
    apply Subtype.ext
    rw [show ((algebraMap K L k : L) : K') = algebraMap K K' k from rfl,
      show ((algebraMap R L (algebraMap K R k) : L) : K')
      = algebraMap R K' (algebraMap K R k) from rfl, halgK'', MvPolynomial.algebraMap_eq,
      MvPolynomial.aeval_C]
  let e' : FractionRing R ≃ₐ[R] L :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun p => rfl)
  have : IsFractionRing R L :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R) e'
  have : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors R)
  have : Algebra.FormallyEtale L K' := Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyEtale R K' := Algebra.FormallyEtale.comp R L K'
  let t₀ : B := ⟨t, htB (Set.mem_singleton t)⟩
  let D₁ : Derivation K R K' := (Algebra.linearMap R K').compDer (MvPolynomial.pderiv t₀)
  have hD₁ : ∀ p : R, D₁ p = algebraMap R K' (MvPolynomial.pderiv t₀ p) := fun _ => rfl
  have hBC := KaehlerDifferential.isBaseChange_of_formallyEtale K R K'
  let Φ : Ω[K'⁄K] →ₗ[K'] K' := hBC.lift D₁.liftKaehlerDifferential
  have hΦ : ∀ p : R, Φ (KaehlerDifferential.D K K' (algebraMap R K' p)) = D₁ p := by
    intro p
    rw [← KaehlerDifferential.map_D K K R K' p]
    change hBC.lift D₁.liftKaehlerDifferential _ = _
    rw [hBC.lift_eq, Derivation.liftKaehlerDifferential_comp_D]
  let δ : Derivation K K' K' := Φ.compDer (KaehlerDifferential.D K K')
  have hδalg : ∀ p : R, δ (algebraMap R K' p) = D₁ p := fun p => hΦ p
  refine ⟨δ, ?_⟩
  have hX : algebraMap R K' (MvPolynomial.X t₀) = t := by
    rw [halgK'', MvPolynomial.aeval_X]
  calc δ t = δ (algebraMap R K' (MvPolynomial.X t₀)) := by rw [hX]
    _ = D₁ (MvPolynomial.X t₀) := hδalg _
    _ = 1 := by rw [hD₁, MvPolynomial.pderiv_X_self, map_one]

end DerivationExistence

section LocalCalc

variable {R K F : Type*} [CommRing R] [Field K] [Field F] [Algebra K F] [Algebra R F]

variable (w : Place K F)

theorem ne_zero_of_ord_ne_zero {f : F} (hf : w.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact hf (Place.ord_zero w)

theorem mem_of_ord_eq_zero {u : F} (hu0 : u ≠ 0) (hu : w.ord u = 0) : u ∈ w.toValuationSubring :=
  (Place.mem_iff_ord_nonneg w hu0).mpr hu.ge

theorem ord_intCast (k : ℤ) : w.ord (k : F) = 0 := by
  rw [show (k : F) = algebraMap K F (k : K) by rw [map_intCast]]
  exact Place.ord_algebraMap w _

theorem le_ord_add {a b : F} {m : ℤ} (ha : a = 0 ∨ m ≤ w.ord a) (hb : b = 0 ∨ m ≤ w.ord b)
    (hab : a + b ≠ 0) : m ≤ w.ord (a + b) := by
  rcases ha with rfl | ha
  · rw [zero_add] at hab ⊢
    exact hb.resolve_left hab
  rcases hb with rfl | hb
  · rw [add_zero]
    exact ha
  by_cases ha0 : a = 0
  · rw [ha0, zero_add] at hab ⊢; exact hb
  by_cases hb0 : b = 0
  · rw [hb0, add_zero]; exact ha
  exact (le_min ha hb).trans (Place.min_ord_le_ord_add w ha0 hb0 hab)

theorem ord_sub_le_ord_apply (D : Derivation R F F)
    (hD : ∀ z ∈ w.toValuationSubring, D z ∈ w.toValuationSubring)
    {π : F} (hπ : w.ord π = 1) {c : ℤ} (hc : 0 ≤ c) (hπD : D π = 0 ∨ 1 - c ≤ w.ord (D π))
    {f : F} (hf : f ≠ 0) (hDf : D f ≠ 0) : w.ord f - c ≤ w.ord (D f) := by
  have hπ0 : π ≠ 0 := ne_zero_of_ord_ne_zero w (by rw [hπ]; exact one_ne_zero)
  set k : ℤ := w.ord f with hk
  have hπk : π ^ k ≠ 0 := zpow_ne_zero k hπ0
  have hπk1 : π ^ (k - 1) ≠ 0 := zpow_ne_zero _ hπ0
  set u : F := f * (π ^ k)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hf (inv_ne_zero hπk)
  have hordu : w.ord u = 0 := by
    rw [hu, Place.ord_mul _ hf (inv_ne_zero hπk), Place.ord_inv, Place.ord_zpow, hπ, mul_one, ← hk]
    ring
  have humem : u ∈ w.toValuationSubring := mem_of_ord_eq_zero w hu0 hordu
  have hDu : D u ∈ w.toValuationSubring := hD u humem
  have hfu : f = u * π ^ k := by
    rw [hu, inv_mul_cancel_right₀ hπk]
  have hDf_eq : D f = π ^ k * D u + u * ((k : F) * π ^ (k - 1) * D π) := by
    conv_lhs => rw [hfu]
    rw [D.leibniz, D.leibniz_zpow]
    simp only [zsmul_eq_mul, smul_eq_mul]
    ring
  have hT1 : π ^ k * D u = 0 ∨ k - c ≤ w.ord (π ^ k * D u) := by
    by_cases hDu0 : D u = 0
    · left; rw [hDu0, mul_zero]
    · right
      rw [Place.ord_mul _ hπk hDu0, Place.ord_zpow, hπ, mul_one]
      have := Place.ord_nonneg_of_mem w hDu
      linarith
  have hT2 : u * ((k : F) * π ^ (k - 1) * D π) = 0 ∨
      k - c ≤ w.ord (u * ((k : F) * π ^ (k - 1) * D π)) := by
    by_cases hz : (k : F) * π ^ (k - 1) * D π = 0
    · left; rw [hz, mul_zero]
    · right
      have hDπ0 : D π ≠ 0 := fun h => hz (by rw [h, mul_zero])
      have hk0 : (k : F) ≠ 0 := fun h => hz (by rw [h, zero_mul, zero_mul])
      have hbound : 1 - c ≤ w.ord (D π) := hπD.resolve_left hDπ0
      rw [Place.ord_mul _ hu0 hz, Place.ord_mul _ (mul_ne_zero hk0 hπk1) hDπ0,
        Place.ord_mul _ hk0 hπk1, hordu, ord_intCast, Place.ord_zpow, hπ, mul_one]
      linarith
  rw [hDf_eq] at hDf ⊢
  exact le_ord_add w hT1 hT2 hDf

theorem ord_le_ord_apply_of_eigen [CharZero F] (D : Derivation R F F)
    (hD : ∀ z ∈ w.toValuationSubring, D z ∈ w.toValuationSubring)
    {φ : F} (hφ0 : φ ≠ 0) (hφ : 0 < w.ord φ) {a : F} (ha : a ∈ w.toValuationSubring)
    (hDφ : D φ = a * φ)
    {z : F} (hz0 : z ≠ 0) (hz : 0 < w.ord z) (hDz : D z ≠ 0) : w.ord z ≤ w.ord (D z) := by
  set k : ℕ := (w.ord φ).toNat with hk
  set m : ℕ := (w.ord z).toNat with hm
  have hkz : (k : ℤ) = w.ord φ := Int.toNat_of_nonneg hφ.le
  have hmz : (m : ℤ) = w.ord z := Int.toNat_of_nonneg hz.le
  have hk1 : 1 ≤ k := by
    have : (1 : ℤ) ≤ k := by rw [hkz]; exact hφ
    exact_mod_cast this
  have hm1 : 1 ≤ m := by
    have : (1 : ℤ) ≤ m := by rw [hmz]; exact hz
    exact_mod_cast this
  have hφm : φ ^ m ≠ 0 := pow_ne_zero _ hφ0
  have hzk : z ^ k ≠ 0 := pow_ne_zero _ hz0
  set u : F := z ^ k * (φ ^ m)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hzk (inv_ne_zero hφm)
  have hordu : w.ord u = 0 := by
    rw [hu, Place.ord_mul _ hzk (inv_ne_zero hφm), Place.ord_inv, ← zpow_natCast, ← zpow_natCast,
      Place.ord_zpow, Place.ord_zpow, ← hkz, ← hmz]
    ring
  have humem : u ∈ w.toValuationSubring := mem_of_ord_eq_zero w hu0 hordu
  have hDu : D u ∈ w.toValuationSubring := hD u humem
  have hzu : z ^ k = u * φ ^ m := by rw [hu, inv_mul_cancel_right₀ hφm]
  have hL : D (z ^ k) = (k : F) * z ^ (k - 1) * D z := by
    rw [D.leibniz_pow, nsmul_eq_mul, smul_eq_mul, mul_assoc]
  have hR : D (u * φ ^ m) = ((m : F) * a * u + D u) * φ ^ m := by
    rw [D.leibniz, D.leibniz_pow, hDφ, smul_eq_mul, smul_eq_mul, nsmul_eq_mul, smul_eq_mul]
    have hpow : φ ^ (m - 1) * φ = φ ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm1]
    calc u * ((m : F) * (φ ^ (m - 1) * (a * φ))) + φ ^ m * D u
        = (m : F) * a * u * (φ ^ (m - 1) * φ) + D u * φ ^ m := by ring
      _ = ((m : F) * a * u + D u) * φ ^ m := by rw [hpow]; ring
  have hEq : (k : F) * z ^ (k - 1) * D z = ((m : F) * a * u + D u) * φ ^ m := by
    rw [← hL, ← hR, hzu]
  have hk0 : (k : F) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hzk1 : z ^ (k - 1) ≠ 0 := pow_ne_zero _ hz0
  have hLne : (k : F) * z ^ (k - 1) * D z ≠ 0 := mul_ne_zero (mul_ne_zero hk0 hzk1) hDz
  have hcoef : (m : F) * a * u + D u ≠ 0 := by
    intro h
    rw [h, zero_mul] at hEq
    exact hLne hEq
  have hcoef_mem : (m : F) * a * u + D u ∈ w.toValuationSubring :=
    add_mem (mul_mem (mul_mem (by
      rw [show ((m : ℕ) : F) = algebraMap K F (m : K) by rw [map_natCast]]
      exact w.algebraMap_mem' _) ha) humem) hDu
  have hcoef_ord : 0 ≤ w.ord ((m : F) * a * u + D u) := Place.ord_nonneg_of_mem w hcoef_mem
  have hordL : w.ord ((k : F) * z ^ (k - 1) * D z) = ((k : ℤ) - 1) * w.ord z + w.ord (D z) := by
    rw [Place.ord_mul _ (mul_ne_zero hk0 hzk1) hDz, Place.ord_mul _ hk0 hzk1, Place.ord_natCast,
      ← zpow_natCast, Place.ord_zpow, Nat.cast_sub hk1]
    push_cast
    ring
  have hordR : w.ord (((m : F) * a * u + D u) * φ ^ m) =
      w.ord ((m : F) * a * u + D u) + (m : ℤ) * w.ord φ := by
    rw [Place.ord_mul _ hcoef hφm, ← zpow_natCast, Place.ord_zpow]
  have key : ((k : ℤ) - 1) * w.ord z + w.ord (D z) = w.ord ((m : F) * a * u + D u) + (m : ℤ) *
    w.ord φ := by
    rw [← hordL, ← hordR, hEq]
  rw [← hkz, ← hmz] at key
  rw [← hmz]
  nlinarith [key, hcoef_ord, hk1, hm1]

end LocalCalc

section Main

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem main [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') := by
  classical
  obtain ⟨x, hx, hxfd⟩ := id hfg
  obtain ⟨x', hx', hxfd'⟩ := id hfg'
  have := hxfd
  have := hxfd'
  have : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K' F').injective
  obtain ⟨g', hg'0, hg'⟩ := hD'
  have hnD' : (n : ℤ) • D' = divOf g' := by
    ext w
    rw [Finsupp.smul_apply, smul_eq_mul, hg' w, divOf_apply hg'0]
  have hlift := Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F K' F' hfg hfg' hgen
  choose lift hliftOver hliftOrd hliftUniq using hlift
  have hU : ∀ (v : Place K F) (w₁ w₂ : Place K' F'), LiesOver w₁ v → LiesOver w₂ v → w₁ = w₂ :=
    fun v w₁ w₂ h₁ h₂ => (hliftUniq v w₁ h₁).trans (hliftUniq v w₂ h₂).symm
  have hV : ∀ (w' : Place K' F') (v₁ v₂ : Place K F), LiesOver w' v₁ → LiesOver w' v₂ → v₁ = v₂ :=
    fun w' v₁ v₂ h₁ h₂ => Place.ext (h₁.symm.trans h₂)
  obtain ⟨P, -⟩ := Place.exists_ord_neg_of_transcendental x hx
  set P₀ : Place K' F' := lift P with hP₀
  have hP₀ : LiesOver P₀ P := hliftOver P
  have hdegP₀ : P₀.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P₀
  set d : ℤ := Divisor.degree D' with hd
  set c₀ : Divisor K' F' := D' - d • Finsupp.single P₀ 1 with hc₀
  have hc₀deg : Divisor.degree c₀ = 0 := by
    simp only [hc₀, map_sub, map_zsmul, Divisor.degree_single, hdegP₀, Nat.cast_one, mul_one,
      smul_eq_mul, hd]
    ring
  obtain ⟨r, fr, hfr0, hfrmem, hfruniq⟩ := exists_reduced (K := K') (F := F') x' hx' c₀ hc₀deg P₀
  set A : Divisor K' F' := c₀ + (r : ℤ) • Finsupp.single P₀ 1 + divOf fr with hA
  have hA0 : 0 ≤ A := divOf_add_mem_lSpace hfr0 hfrmem
  have hA0w : ∀ w : Place K' F', 0 ≤ A w := fun w => by simpa using hA0 w
  set φ : F' := g' * fr ^ n with hφ
  have hφ0 : φ ≠ 0 := mul_ne_zero hg'0 (pow_ne_zero _ hfr0)
  have hφdiv : divOf φ = (n : ℤ) • A - ((n : ℤ) * ((r : ℤ) - d)) • Finsupp.single P₀ 1 := by
    rw [hφ, divOf_mul hg'0 (pow_ne_zero _ hfr0), divOf_pow, ← hnD']
    simp only [hA, hc₀]
    module
  have hordφ : ∀ w : Place K' F',
      w.ord φ = (n : ℤ) * A w - (n : ℤ) * ((r : ℤ) - d) * Finsupp.single P₀ (1 : ℤ) w := by
    intro w
    have := congrArg (fun E : Divisor K' F' => E w) hφdiv
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, divOf_apply hφ0] at this
    rw [this, mul_assoc]
  have hordφ_gen : ∀ w : Place K' F', IsGeneric K F w → w.ord φ = (n : ℤ) * A w := by
    intro w hw
    have hsP₀ : Finsupp.single P₀ (1 : ℤ) w = 0 := by
      rw [Finsupp.single_apply, ite_eq_right]
      rintro rfl
      exact hw P hP₀
    rw [hordφ, hsP₀, mul_zero, sub_zero]
  have hAsupp : ∀ w' ∈ A.support, ¬ IsGeneric K F w' := by
    intro w' hw' hgw
    obtain ⟨t, ht⟩ := hgw.exists_inMax_sub x
    have htK : t ∉ Set.range (algebraMap K K') := hgw.not_mem_range x hx ht
    have httr : Transcendental K t := transcendental_of_not_mem_range htK
    obtain ⟨δ, hδt⟩ := exists_derivation_apply_eq_one K K' t httr
    obtain ⟨Dd, hDF, hDE, hDreg⟩ :=
      AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem K F K' F' hfg hfg' hgen δ
    set y : F' := Dd φ * φ⁻¹ with hy
    have hymem : y ∈ LSpace A := by
      rw [mem_lSpace_iff_ord]
      rcases eq_or_ne y 0 with hy0 | hy0
      · exact Or.inl hy0
      right
      intro w
      have hDφ0 : Dd φ ≠ 0 := by
        intro h; apply hy0; rw [hy, h, zero_mul]
      have hordy : w.ord y = w.ord (Dd φ) - w.ord φ := by
        rw [hy, Place.ord_mul _ hDφ0 (inv_ne_zero hφ0), Place.ord_inv]; ring
      by_cases hgen_w : IsGeneric K F w
      · obtain ⟨π, hπ⟩ := Place.exists_ord_eq_one w
        have hπ0 : π ≠ 0 := ne_zero_of_ord_ne_zero w (by rw [hπ]; exact one_ne_zero)
        have hπmem : π ∈ w.toValuationSubring :=
          (Place.mem_iff_ord_nonneg w hπ0).mpr (by rw [hπ]; exact zero_le_one)
        have hDπ : Dd π = 0 ∨ 1 - 1 ≤ w.ord (Dd π) := by
          by_cases h : Dd π = 0
          · exact Or.inl h
          · right
            rw [sub_self]
            exact Place.ord_nonneg_of_mem w (hDreg w π hπmem)
        have h1 : w.ord φ - 1 ≤ w.ord (Dd φ) :=
          ord_sub_le_ord_apply w Dd (fun z hz => hDreg w z hz) hπ zero_le_one hDπ hφ0 hDφ0
        have hordφw : w.ord φ = (n : ℤ) * A w := hordφ_gen w hgen_w
        by_cases hAw : A w = 0
        · have hφmem : φ ∈ w.toValuationSubring :=
            (Place.mem_iff_ord_nonneg w hφ0).mpr (by rw [hordφw, hAw, mul_zero])
          have h2 := Place.ord_nonneg_of_mem w (hDreg w φ hφmem)
          rw [hordy, hordφw, hAw]
          linarith
        · have hAw1 : 1 ≤ A w := by
            have := hA0w w
            omega
          rw [hordy]
          linarith
      · simp only [IsGeneric, not_forall, not_not] at hgen_w
        obtain ⟨v, hv⟩ := hgen_w
        have hw : w = lift v := hU v w (lift v) hv (hliftOver v)
        obtain ⟨π₀, hπ₀⟩ := Place.exists_ord_eq_one v
        have hπ : w.ord (algebraMap F F' π₀) = 1 := by rw [hw, hliftOrd, hπ₀]
        have hDπ : Dd (algebraMap F F' π₀) = 0 ∨ 1 - 0 ≤ w.ord (Dd (algebraMap F F' π₀)) :=
          Or.inl (hDF π₀)
        have h1 : w.ord φ - 0 ≤ w.ord (Dd φ) :=
          ord_sub_le_ord_apply w Dd (fun z hz => hDreg w z hz) hπ le_rfl hDπ hφ0 hDφ0
        have h2 := hA0w w
        rw [hordy]
        linarith
    have hyfr : y * fr ∈ LSpace (c₀ + (r : ℤ) • Finsupp.single P₀ 1) := by
      rw [hA] at hymem
      exact (mem_lSpace_add_divOf_iff hfr0).mp hymem
    obtain ⟨a, ha⟩ := hfruniq _ hyfr
    have hya : y = algebraMap K' F' a := by
      rw [Algebra.smul_def] at ha
      exact (mul_left_injective₀ hfr0 ha).symm
    have hDφ : Dd φ = algebraMap K' F' a * φ := by
      rw [← hya, hy, inv_mul_cancel_right₀ hφ0]
    have hAw' : 1 ≤ A w' := by
      have h1 := hA0w w'
      have h2 : A w' ≠ 0 := Finsupp.mem_support_iff.mp hw'
      omega
    have hn1 : (1 : ℤ) ≤ n := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    have hφpos : 0 < w'.ord φ := by
      rw [hordφ_gen w' hgw]
      nlinarith
    have hDy₀ : Dd (algebraMap F F' x - algebraMap K' F' t) = -1 := by
      rw [map_sub, hDF, hDE, hδt, map_one, zero_sub]
    rcases ht with hy00 | hy0pos
    · rw [hy00, map_zero] at hDy₀
      norm_num at hDy₀
    · have hy0ne : algebraMap F F' x - algebraMap K' F' t ≠ 0 := by
        intro h
        rw [h, Place.ord_zero] at hy0pos
        exact lt_irrefl _ hy0pos
      have hDy₀ne : Dd (algebraMap F F' x - algebraMap K' F' t) ≠ 0 := by
        rw [hDy₀]; norm_num
      have key := ord_le_ord_apply_of_eigen w' Dd (fun z hz => hDreg w' z hz) hφ0 hφpos
        (w'.algebraMap_mem' a) hDφ hy0ne hy0pos hDy₀ne
      rw [hDy₀, show (-1 : F') = algebraMap K' F' (-1) by rw [map_neg, map_one],
        Place.ord_algebraMap] at key
      exact absurd key (not_le.mpr hy0pos)
  set B : Divisor K' F' := A + (d - r) • Finsupp.single P₀ 1 with hB
  have hBsupp : ∀ w' ∈ B.support, ∃ v : Place K F, LiesOver w' v := by
    intro w' hw'
    rcases Finset.mem_union.mp (Finsupp.support_add hw') with h | h
    · have := hAsupp w' h
      simp only [IsGeneric, not_forall, not_not] at this
      exact this
    · have h2 := Finsupp.support_smul h
      rw [Finsupp.mem_support_single] at h2
      exact ⟨P, h2.1 ▸ hP₀⟩
  have hD'B : D' = B + divOf fr⁻¹ := by
    rw [divOf_inv]
    simp only [hB, hA, hc₀, sub_smul]
    abel
  let π : Place K' F' → Place K F := fun w' =>
    if h : ∃ v : Place K F, LiesOver w' v then h.choose else P
  have hπ : ∀ (w' : Place K' F') (v : Place K F), LiesOver w' v → π w' = v := by
    intro w' v h
    have hex : ∃ v : Place K F, LiesOver w' v := ⟨v, h⟩
    simp only [π, dite_eq_left hex]
    exact hV w' _ _ hex.choose_spec h
  set R₀ : Divisor K F := Finsupp.mapDomain π B with hR₀
  have hR₀v : ∀ v : Place K F, R₀ v = B (lift v) := by
    intro v
    have hS : ((B.support : Finset (Place K' F')) : Set (Place K' F')) ⊆
        {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := fun w' hw' => hBsupp w' hw'
    have hinjOn : Set.InjOn π {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := by
      rintro w₁ ⟨v₁, h₁⟩ w₂ ⟨v₂, h₂⟩ heq
      rw [hπ w₁ v₁ h₁, hπ w₂ v₂ h₂] at heq
      subst heq
      exact hU v₁ w₁ w₂ h₁ h₂
    have := Finsupp.mapDomain_apply' _ B hS hinjOn (a := lift v) ⟨v, hliftOver v⟩
    rwa [hπ (lift v) v (hliftOver v)] at this
  have hB0 : ∀ w' : Place K' F', (∀ v : Place K F, ¬ LiesOver w' v) → B w' = 0 := by
    intro w' hw'
    by_contra hne
    obtain ⟨v, hv⟩ := hBsupp w' (Finsupp.mem_support_iff.mpr hne)
    exact hw' v hv
  have hprin : ((n : ℤ) • R₀).IsPrincipal := by
    apply Divisor.isPrincipal_of_constantFieldExtension K F K' F' hfg hfg' hgen
      ((n : ℤ) • R₀) ((n : ℤ) • B)
    · intro w' v hw'v
      have hw : w' = lift v := hU v w' (lift v) hw'v (hliftOver v)
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [hR₀v v, hw]
    · intro w' hw'
      simp only [Finsupp.smul_apply, smul_eq_mul, hB0 w' hw', mul_zero]
    · refine isPrincipal_iff_eq_divOf.mpr ⟨g' * fr ^ n, mul_ne_zero hg'0 (pow_ne_zero _ hfr0), ?_⟩
      rw [divOf_mul hg'0 (pow_ne_zero _ hfr0), divOf_pow, ← hnD']
      have : B = D' + divOf fr := by
        rw [hD'B, divOf_inv]
        abel
      rw [this, smul_add]
  obtain ⟨g, hg0, hg⟩ := hprin
  refine ⟨R₀, fr⁻¹, inv_ne_zero hfr0, ⟨g, hg0, fun v => ?_⟩, fun v v' hv' => ?_, fun v' hv' => ?_⟩
  · have := hg v
    simpa only [Finsupp.smul_apply, smul_eq_mul] using this
  · have hw : v' = lift v := hU v v' (lift v) hv' (hliftOver v)
    rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0), hw, hR₀v v]
  · rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0), hB0 v' hv', zero_add]

end Main

end TorsionDescentDeriv

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') :=
  AlgebraicCurve.TorsionDescentDeriv.main hfg hfg' hgen n hn D' hD'
end AlgebraicCurves.Divisors.Proofs.Divisor_exists_torsion_descent_of_constantFieldExtension
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
