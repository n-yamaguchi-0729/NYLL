/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDeg
import Nyll.AlgebraicCurves.Differentials.Maps.OrdDifferentialMapEq
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteSimpleExtensions
import Nyll.AlgebraicCurves.Places.Orders.OrdNegTranscendental

/-!
# Surjective algebra Map of injective restrict place of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve IntermediateField

namespace P2mKcDegreeOneByInjectivePlaces

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact _root_.AlgebraicCurve.Place.mem_of_ord_nonneg v hf h

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  _root_.AlgebraicCurve.Place.ord_nonneg_of_mem v hf

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {f : F} (hf : 0 < v.ord f) :
    ∃ h : f ∈ v.toValuationSubring,
      (⟨f, h⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  have hmem : f ∈ v.toValuationSubring := mem_of_ord_nonneg v hf.le
  refine ⟨hmem, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem isUnit_algebraMap (v : Place K F) {a : K} (ha : a ≠ 0) :
    IsUnit (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h]
  exact (ha.isUnit).map _

theorem eq_of_ord_sub_algebraMap_pos (v : Place K F) (t : F) {c c' : K}
    (hc : 0 < v.ord (t - algebraMap K F c)) (hc' : 0 < v.ord (t - algebraMap K F c')) :
    c = c' := by
  by_contra hne
  obtain ⟨h1, hm1⟩ := mem_maximalIdeal_of_ord_pos v hc
  obtain ⟨h2, hm2⟩ := mem_maximalIdeal_of_ord_pos v hc'
  have hsub := Ideal.sub_mem _ hm2 hm1
  have hval : ((⟨t - algebraMap K F c', h2⟩ : v.toValuationSubring)
        - ⟨t - algebraMap K F c, h1⟩)
      = ⟨algebraMap K F (c - c'), v.algebraMap_mem' (c - c')⟩ := by
    apply Subtype.ext
    change (t - algebraMap K F c') - (t - algebraMap K F c) = algebraMap K F (c - c')
    rw [map_sub]
    ring
  rw [hval] at hsub
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hsub) (isUnit_algebraMap v (sub_ne_zero.mpr hne))

end PlaceFacts

section TotalRamification

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

theorem ramificationIndex_eq_finrank [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hinj : Function.Injective (fun w : Place K F' => w.restrict F)) (w : Place K F') :
    w.ramificationIndex F = Module.finrank F F' := by
  have hfib : (w.restrict F).fiber F' = {w} := by
    ext w'
    rw [Place.mem_fiber, Finset.mem_singleton]
    exact ⟨fun h => hinj h, fun h => h ▸ rfl⟩
  have hid := Place.sum_ramificationIndex_mul_inertiaDeg (K := K) (F := F) (F' := F')
    (w.restrict F)
  rw [hfib, Finset.sum_singleton] at hid
  have hdeg : w.inertiaDeg F = 1 := by
    have h := w.deg_restrict_mul_inertiaDeg (F := F)
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
      one_mul] at h
    exact h
  rw [hdeg, Nat.cast_one, mul_one] at hid
  exact_mod_cast hid

end TotalRamification

section Finiteness

theorem differentialCoeff_D_regular {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ w : Place K F', w.DCoordGenerates]
    (w : Place K F') (u : F') (_hu : u ≠ 0) (hord : w.ord u = 0) :
    w.differentialCoeff (KaehlerDifferential.D K F' u) = 0 ∨
      0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) := by
  right
  have humem : u ∈ w.toValuationSubring := mem_of_ord_nonneg w (le_of_eq hord.symm)
  obtain ⟨c, hc, hD⟩ := exists_mem_D_eq_smul_D_of_isCurveOver w w.ord_uniformizer humem
  rw [← Place.dCoord_eq] at hD
  rw [w.differentialCoeff_unique hD]
  exact ord_nonneg_of_mem w hc

theorem finite_place_of_one_lt (K F F' : Type) [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F']
    [Algebra.EssFiniteType K F'] [Module.Finite F F']
    (hinj : Function.Injective (fun w : Place K F' => w.restrict F))
    (hn : 1 < Module.finrank F F') : Finite (Place K F') := by
  classical
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  have hDC : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hDC' : ∀ w : Place K F', w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  have : HasCanonicalDivisor (K := K) (F := F') := hasCanonicalDivisor_of_isCurveOver
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  have he : ∀ w : Place K F', w.ramificationIndex F = Module.finrank F F' :=
    ramificationIndex_eq_finrank hinj
  have htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w => by
    exact_mod_cast (w.ramificationIndex_pos (F := F)).ne'
  have hmap : ∀ w : Place K F', w.ordDifferential (KaehlerDifferential.map K K F F' ω₀)
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + ((w.ramificationIndex F : ℤ) - 1) := fun w =>
    ordDifferential_map_eq (K := K) (F := F) (F' := F')
      (fun w u hu hord => differentialCoeff_D_regular w u hu hord) htame hω₀ w
  obtain ⟨D₀, hD₀⟩ := HasCanonicalDivisor.exists_divisor ω₀ hω₀
  have hD₁ : ∃ D₁ : Divisor K F',
      ∀ w, D₁ w = w.ordDifferential (KaehlerDifferential.map K K F F' ω₀) := by
    by_cases h0 : KaehlerDifferential.map K K F F' ω₀ = 0
    · refine ⟨0, fun w => ?_⟩
      rw [h0, Place.ordDifferential, Place.differentialCoeff_zero, Place.ord_zero]
      rfl
    · exact HasCanonicalDivisor.exists_divisor _ h0
  obtain ⟨D₁, hD₁⟩ := hD₁
  have hcover : (Set.univ : Set (Place K F')) ⊆
      (D₁.support : Set (Place K F')) ∪
        (fun w : Place K F' => w.restrict F) ⁻¹' (D₀.support : Set (Place K F)) := by
    intro w _
    by_contra hw
    simp only [Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_preimage,
      not_or, not_not] at hw
    have h := hmap w
    rw [← hD₁, ← hD₀, hw.1, hw.2, he w, mul_zero, zero_add] at h
    have h' : (Module.finrank F F' : ℤ) = 1 := by linarith
    have : Module.finrank F F' = 1 := by exact_mod_cast h'
    omega
  have hfin : (Set.univ : Set (Place K F')).Finite :=
    ((D₁.support.finite_toSet).union
      ((D₀.support.finite_toSet).preimage hinj.injOn)).subset hcover
  exact Set.finite_univ_iff.mp hfin

end Finiteness

section Infinitude

theorem infinite_place (K F' : Type) [Field K] [Field F'] [Algebra K F'] [IsAlgClosed K]
    [CharZero K] [IsCurveOver K F'] [Algebra.EssFiniteType K F'] : Infinite (Place K F') := by
  obtain ⟨t, ht, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F')
  have := hfin
  have key : ∀ c : K, ∃ w : Place K F', 0 < w.ord (t - algebraMap K F' c) := by
    intro c
    have hy : Transcendental K (t - algebraMap K F' c)⁻¹ := by
      intro halg
      apply ht
      have h1 : IsAlgebraic K (t - algebraMap K F' c) := IsAlgebraic.inv_iff.mp halg
      have h2 : IsAlgebraic K (t - algebraMap K F' c + algebraMap K F' c) :=
        h1.add (isAlgebraic_algebraMap c)
      simpa using h2
    have : FiniteDimensional K⟮(t - algebraMap K F' c)⁻¹⟯ F' :=
      finiteDimensional_adjoin_of_transcendental t hy
    obtain ⟨w, hw⟩ := Place.exists_ord_neg_of_transcendental (t - algebraMap K F' c)⁻¹ hy
    refine ⟨w, ?_⟩
    rw [Place.ord_inv] at hw
    omega
  choose w hw using key
  refine Infinite.of_injective w fun c c' h => ?_
  have h1 := hw c
  have h2 := hw c'
  rw [← h] at h2
  exact eq_of_ord_sub_algebraMap_pos (w c) t h1 h2

end Infinitude

end P2mKcDegreeOneByInjectivePlaces

open P2mKcDegreeOneByInjectivePlaces in
theorem _root_.AlgebraicCurve.surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
    (K F F' : Type) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
      [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F']
      [Algebra.EssFiniteType K F']
    [Module.Finite F F']
    (hinj : Function.Injective (fun w : Place K F' => w.restrict F)) :
    Function.Surjective (algebraMap F F') := by
  by_contra hns
  have hn : 1 < Module.finrank F F' := by
    have hpos : 0 < Module.finrank F F' := Module.finrank_pos
    rcases (Nat.succ_le_of_lt hpos).eq_or_lt with h1 | h1
    · exact absurd ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp h1.symm).2 hns
    · exact h1
  have := finite_place_of_one_lt K F F' hinj hn
  exact (infinite_place K F').not_finite ‹_›
end AlgebraicCurves.Places.Proofs.Surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
end ProofImplementation

attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
