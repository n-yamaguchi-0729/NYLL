/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Places.Evaluation.Value
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# Exists mem riemann Roch Space forall has Value mul of exists not mem
-/

section ProofImplementation


namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsMemRRSpaceAllHasValueMul

open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace EvalCount
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_zero_of_ord_pos (v : Place K F) {f : F} (h : f = 0 ∨ 0 < v.ord f) :
    v.HasValue f 0 := by
  rcases h with rfl | h
  · exact Place.hasValue_zero v
  · have hf : f ≠ 0 := by
      rintro rfl
      exact (lt_irrefl (0 : ℤ)) (v.ord_zero ▸ h)
    have hlt : v.adicValuation f < 1 := by
      rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hmem : f ∈ v.toValuationSubring := v.mem_iff_adicValuation_le_one.mpr hlt.le
    refine ⟨hmem, ?_⟩
    have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
    rw [map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hmax

theorem riemannRochSpace_mono {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (Finsupp.le_def.mp h v)).trans h0)

theorem ne_zero_and_ord_add_eq_zero {D : Divisor K F} {f : F} {w : Place K F}
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    f ≠ 0 ∧ w.ord f + D w = 0 := by
  rw [mem_riemannRochSpace_iff] at hf hf'
  push Not at hf'
  obtain ⟨v, hf0, hv⟩ := hf'
  have hvw : v = w := by
    by_contra hne
    have h1 : (D - Finsupp.single w 1 : Divisor K F) v = D v := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hne, sub_zero]
    rcases hf v with h | h
    · exact hf0 h
    · rw [h1] at hv
      exact absurd h (not_le.mpr hv)
  subst hvw
  refine ⟨hf0, ?_⟩
  rcases hf v with h | h
  · exact absurd h hf0
  · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hv
    omega

theorem exists_mem_riemannRochSpace_not_mem_of_finrank_lt {D D' : Divisor K F}
    [FiniteDimensional K ↥(riemannRochSpace D')]
    (h : Module.finrank K ↥(riemannRochSpace D') < Module.finrank K ↥(riemannRochSpace D)) :
    ∃ p ∈ riemannRochSpace D, p ∉ riemannRochSpace D' := by
  by_contra hcon
  push Not at hcon
  have hle : riemannRochSpace D ≤ riemannRochSpace D' := fun p hp => hcon p hp
  exact absurd (LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle))
    (not_le.mpr h)

theorem twist_mul_mem {E : Divisor K F} {v : Place K F} {t p : F} (ht0 : t ≠ 0) (ht : v.ord t = E v)
    (hp : p ∈ riemannRochSpace E) : t * p ∈ v.toValuationSubring := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [mul_zero]; exact zero_mem _
  · apply (v.mem_iff_ord_nonneg (mul_ne_zero ht0 hp0)).mpr
    rcases (mem_riemannRochSpace_iff.mp hp) v with h | h
    · exact absurd h hp0
    · rw [v.ord_mul ht0 hp0, ht]
      omega

theorem exists_hasValue_twist_mul {E : Divisor K F} {v : Place K F} {t p : F}
    (hrat : Function.Surjective (algebraMap K v.ResidueField))
    (ht0 : t ≠ 0) (ht : v.ord t = E v) (hp : p ∈ riemannRochSpace E) :
    ∃ a : K, v.HasValue (t * p) a := by
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hrat (twist_mul_mem ht0 ht hp)
  exact ⟨a, ha⟩

section Closed

variable [IsAlgClosed K] [IsCurveOver K F]

theorem surjective_algebraMap_residueField (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  have : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end Closed

end AlgebraicCurve.EvalCount

theorem _root_.AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Divisor k F) (v : ι → Place k F) (hv : Function.Injective v) (t : ι → F)
    (ht : ∀ i, t i ≠ 0 ∧ (v i).ord (t i) = E (v i))
    (hstep : ∀ i, ∃ g ∈ riemannRochSpace (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) 1),
      g ∉ riemannRochSpace (E - ∑ j, Finsupp.single (v j) 1))
    (c : ι → k) :
    ∃ p ∈ riemannRochSpace E, ∀ i, (v i).HasValue (t i * p) (c i) := by
  classical
  choose g hg hg' using hstep
  have hS : ∀ (s : Finset ι) (l : ι), (∑ j ∈ s, Finsupp.single (v j) (1 : ℤ)) (v l) = if l ∈ s
    then 1 else 0 := by
    intro s l
    rw [Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply, hv.eq_iff]
    rw [Finset.sum_ite_eq']
  have hSnonneg : ∀ s : Finset ι, (0 : Divisor k F) ≤ ∑ j ∈ s, Finsupp.single (v j) (1 : ℤ) :=
    fun s => Finset.sum_nonneg fun j _ => Finsupp.single_nonneg.mpr zero_le_one
  have hEfull : ∀ i, E - ∑ j, Finsupp.single (v j) (1 : ℤ)
      = (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) 1) - Finsupp.single (v i) 1 := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), sub_sub]
  have hkey : ∀ i, g i ≠ 0 ∧ (v i).ord (g i) = - E (v i) := by
    intro i
    have h := AlgebraicCurve.EvalCount.ne_zero_and_ord_add_eq_zero (hg i)
      (by rw [← hEfull i]; exact hg' i)
    refine ⟨h.1, ?_⟩
    have hc : (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) (1 : ℤ)) (v i) = E (v i) := by
      rw [Finsupp.sub_apply, hS]
      rw [ite_eq_right (Finset.notMem_erase i Finset.univ), sub_zero]
    rw [hc] at h
    omega
  have hoff : ∀ i l, l ≠ i → -E (v l) + 1 ≤ (v l).ord (g i) := by
    intro i l hl
    rcases (mem_riemannRochSpace_iff.mp (hg i)) (v l) with h | h
    · exact absurd h (hkey i).1
    · rw [Finsupp.sub_apply, hS, ite_eq_left (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)] at h
      omega
  have hdiag : ∀ i, ∃ a : k, a ≠ 0 ∧ (v i).HasValue (t i * g i) a := by
    intro i
    have hne : t i * g i ≠ 0 := mul_ne_zero (ht i).1 (hkey i).1
    have h0 : (v i).ord (t i * g i) = 0 := by
      rw [(v i).ord_mul (ht i).1 (hkey i).1, (ht i).2, (hkey i).2]; ring
    obtain ⟨hm, hu⟩ := (v i).exists_isUnit_of_ord_eq_zero hne h0
    obtain ⟨a, ha, hane⟩ := (v i).exists_hasValue_of_surjective
      (AlgebraicCurve.EvalCount.surjective_algebraMap_residueField _) hm
    exact ⟨a, hane hu, ha⟩
  choose a ha0 ha using hdiag
  have hzero : ∀ i l, l ≠ i → (v l).HasValue (t l * g i) 0 := by
    intro i l hl
    apply AlgebraicCurve.EvalCount.hasValue_zero_of_ord_pos
    right
    rw [(v l).ord_mul (ht l).1 (hkey i).1, (ht l).2]
    have := hoff i l hl
    omega
  refine ⟨∑ j, (c j * (a j)⁻¹) • g j, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact AlgebraicCurve.EvalCount.riemannRochSpace_mono (sub_le_self _ (hSnonneg _)) (hg j)
  · intro i
    have hsum := Place.HasValue.sum (v := v i) Finset.univ
      (g := fun j => (c j * (a j)⁻¹) • (t i * g j))
      (a := fun j => (c j * (a j)⁻¹) * (if j = i then a j else 0)) (fun j _ => by
        by_cases hji : j = i
        · subst hji
          rw [ite_eq_left rfl]
          exact (ha j).smul _
        · rw [ite_eq_right hji]
          exact (hzero j i (Ne.symm hji)).smul (c j * (a j)⁻¹))
    have hval : (∑ j, (c j * (a j)⁻¹) * (if j = i then a j else 0)) = c i := by
      simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i), inv_mul_cancel_right₀ (ha0 i)]
    rw [hval] at hsum
    have e : t i * ∑ j, (c j * (a j)⁻¹) • g j = ∑ j, (c j * (a j)⁻¹) • (t i * g j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm]
    rw [e]
    exact hsum
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsMemRRSpaceAllHasValueMul
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
