/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Places.Evaluation.Value
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.MemRiemannRochSpaceHasValueMul

/-!
# Finrank add card le of forall exists mem riemann Roch Space has Value mul
-/

section ProofImplementation


namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FinrankAddCardLeAllExistsMemRR

open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs

open _root_.AlgebraicCurve

open ExistsMemRRSpaceAllHasValueMul


theorem _root_.AlgebraicCurve.finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
    {ι : Type*} [Fintype ι]
    (E₁ E₂ : Divisor k F)
    [FiniteDimensional k ↥(riemannRochSpace E₁)] [FiniteDimensional k ↥(riemannRochSpace E₂)]
    (v₁ v₂ : ι → Place k F) (t₁ t₂ : ι → F)
    (ht₁ : ∀ i, t₁ i ≠ 0 ∧ (v₁ i).ord (t₁ i) = E₁ (v₁ i))
    (ht₂ : ∀ i, t₂ i ≠ 0 ∧ (v₂ i).ord (t₂ i) = E₂ (v₂ i))
    (lam : ι → k)
    (hsurj : ∀ c : ι → k, ∃ p ∈ riemannRochSpace E₁, ∀ i, (v₁ i).HasValue (t₁ i * p) (c i))
    (T : Submodule k (F × F))
    (hT : ∀ p, p ∈ T ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : k, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c) :
    FiniteDimensional k ↥T ∧
      Module.finrank k ↥T + Fintype.card ι ≤
        Module.finrank k ↥(riemannRochSpace E₁) + Module.finrank k ↥(riemannRochSpace E₂) := by
  classical
  have hex₁ : ∀ (p : ↥(riemannRochSpace E₁)) (i : ι), ∃ a : k, (v₁ i).HasValue (t₁ i * (p : F)) a :=
    fun p i => AlgebraicCurve.EvalCount.exists_hasValue_twist_mul
      (AlgebraicCurve.EvalCount.surjective_algebraMap_residueField _)
      (ht₁ i).1 (ht₁ i).2 p.2
  have hex₂ : ∀ (p : ↥(riemannRochSpace E₂)) (i : ι), ∃ a : k, (v₂ i).HasValue (t₂ i * (p : F)) a :=
    fun p i => AlgebraicCurve.EvalCount.exists_hasValue_twist_mul
      (AlgebraicCurve.EvalCount.surjective_algebraMap_residueField _)
      (ht₂ i).1 (ht₂ i).2 p.2
  choose val₁ hval₁ using hex₁
  choose val₂ hval₂ using hex₂
  let V₁ : ↥(riemannRochSpace E₁) →ₗ[k] (ι → k) :=
    { toFun := val₁
      map_add' := fun p q => funext fun i => (hval₁ (p + q) i).unique (by
        have h := (hval₁ p i).add (hval₁ q i)
        rwa [← mul_add] at h)
      map_smul' := fun c p => funext fun i => (hval₁ (c • p) i).unique (by
        have h := (hval₁ p i).smul c
        rwa [← mul_smul_comm] at h) }
  let V₂ : ↥(riemannRochSpace E₂) →ₗ[k] (ι → k) :=
    { toFun := val₂
      map_add' := fun p q => funext fun i => (hval₂ (p + q) i).unique (by
        have h := (hval₂ p i).add (hval₂ q i)
        rwa [← mul_add] at h)
      map_smul' := fun c p => funext fun i => (hval₂ (c • p) i).unique (by
        have h := (hval₂ p i).smul c
        rwa [← mul_smul_comm] at h) }
  let Dg : (ι → k) →ₗ[k] (ι → k) := LinearMap.pi fun i => lam i • LinearMap.proj i
  let Φ : (↥(riemannRochSpace E₁) × ↥(riemannRochSpace E₂)) →ₗ[k] (ι → k) :=
    V₁.comp (LinearMap.fst k _ _) - Dg.comp (V₂.comp (LinearMap.snd k _ _))
  have hΦ : ∀ (p : ↥(riemannRochSpace E₁)) (q : ↥(riemannRochSpace E₂)) (i : ι),
      Φ (p, q) i = val₁ p i - lam i * val₂ q i := by
    intro p q i
    change val₁ p i - lam i • val₂ q i = _
    rw [smul_eq_mul]
  let j : ↥T →ₗ[k] (↥(riemannRochSpace E₁) × ↥(riemannRochSpace E₂)) :=
    { toFun := fun x => (⟨x.1.1, ((hT x.1).mp x.2).1⟩, ⟨x.1.2, ((hT x.1).mp x.2).2.1⟩)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => ((z.1 : ↥(riemannRochSpace E₁)) : F)) h
    · exact congrArg (fun z => ((z.2 : ↥(riemannRochSpace E₂)) : F)) h
  have hjker : ∀ x : ↥T, j x ∈ LinearMap.ker Φ := by
    intro x
    obtain ⟨-, -, hx⟩ := (hT x.1).mp x.2
    rw [LinearMap.mem_ker]
    funext i
    obtain ⟨c, hc₁, hc₂⟩ := hx i
    rw [hΦ, Pi.zero_apply]
    have e₁ : val₁ (j x).1 i = lam i * c := (hval₁ (j x).1 i).unique hc₁
    have e₂ : val₂ (j x).2 i = c := (hval₂ (j x).2 i).unique hc₂
    rw [e₁, e₂, sub_self]
  have hfinT : FiniteDimensional k ↥T := Module.Finite.of_injective j hj
  let j' : ↥T →ₗ[k] ↥(LinearMap.ker Φ) := LinearMap.codRestrict (LinearMap.ker Φ) j hjker
  have hj' : Function.Injective j' := fun x y h => hj (congrArg Subtype.val h)
  have hT_le : Module.finrank k ↥T ≤ Module.finrank k ↥(LinearMap.ker Φ) :=
    LinearMap.finrank_le_finrank_of_injective hj'
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro d
    obtain ⟨p, hp, hpv⟩ := hsurj d
    refine ⟨(⟨p, hp⟩, 0), funext fun i => ?_⟩
    rw [hΦ]
    have e₁ : val₁ ⟨p, hp⟩ i = d i := (hval₁ _ i).unique (hpv i)
    have e₂ : val₂ 0 i = 0 := by
      have h := congrFun (map_zero V₂) i
      exact h
    rw [e₁, e₂, mul_zero, sub_zero]
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_prod] at hrank
  refine ⟨hfinT, ?_⟩
  omega
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FinrankAddCardLeAllExistsMemRR
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
