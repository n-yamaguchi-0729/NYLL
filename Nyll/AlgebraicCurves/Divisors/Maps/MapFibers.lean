/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

Anthropic FLT material was identified by code comparison in the following original
modules; their exact source-file correspondence remains unresolved:
- Divisor_pushforwardAlong_single_one
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardAlong_single_one_of_isAlgClosed.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_one_eq_sum.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Places.Residue.ModuleFiniteResidueFieldRestrict
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegAlong

/-!
# Map Fibers
-/

section

/-!
# Divisor pushforward Along single one
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_single_one

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_single_one
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : AlgebraicCurve.Place K F')
    (hW : W.deg = 1) (hV : (W.restrictAlong ψ hψ).deg = 1) :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by
  have h1 : W.inertiaDegAlong ψ hψ = 1 := by
    let := algebraAlong ψ
    have := isScalarTower_along ψ
    have := isIntegral_along ψ hψ
    have ht : (W.restrictAlong ψ hψ).deg * W.inertiaDegAlong ψ hψ = W.deg :=
      W.deg_restrict_mul_inertiaDeg (F := F)
    rw [hV, hW, one_mul] at ht
    exact ht
  rw [Divisor.pushforwardAlong_single, h1, Nat.cast_one, mul_one]
end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_single_one
end ProofImplementation

end

section

/-!
# Divisor pushforward Along single one of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_single_one_of_isAlgClosed

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_single_one_of_isAlgClosed
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.IsCurveOver K F]
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (W : AlgebraicCurve.Place K F') :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by
  let := algebraAlong ψ
  have := isScalarTower_along ψ
  have := isIntegral_along ψ hψ
  have : Module.Finite F F' := hfin
  have := AlgebraicCurve.Place.module_finite_residueField_restrict K F F' W
  have := IsCurveOver.finiteResidue (K := K) (W.restrict F)
  have : Module.Finite K W.ResidueField := Module.Finite.trans (W.restrict F).ResidueField _
  have hW : W.deg = 1 := W.deg_eq_one_of_isAlgClosed_of_finite
  have hV : (W.restrictAlong ψ hψ).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed _
  have h1 : W.inertiaDegAlong ψ hψ = 1 := by
    have ht : (W.restrictAlong ψ hψ).deg * W.inertiaDegAlong ψ hψ = W.deg :=
      W.deg_restrict_mul_inertiaDeg (F := F)
    rw [hV, hW, one_mul] at ht
    exact ht
  rw [Divisor.pushforwardAlong_single, h1, Nat.cast_one, mul_one]
end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_single_one_of_isAlgClosed
end ProofImplementation

end

section

/-!
# Divisor exists pullback Along single one eq sum
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_exists_pullbackAlong_single_one_eq_sum

namespace PullbackEnum

theorem exists_fin_sum_eq_sum_nsmul {α M : Type*} [AddCommMonoid M] (s : Finset α)
    (e : α → ℕ) (f : α → M) :
    ∀ n : ℕ, ∑ a ∈ s, e a = n →
      ∃ W : Fin n → α, (∀ i, W i ∈ s) ∧ ∑ i, f (W i) = ∑ a ∈ s, e a • f a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n hn
    rw [Finset.sum_empty] at hn
    subst hn
    exact ⟨Fin.elim0, fun i => i.elim0, by simp only [Finset.univ_eq_empty, Finset.sum_empty]⟩
  | insert a s ha ih =>
    intro n hn
    rw [Finset.sum_insert ha] at hn
    obtain ⟨W, hW, hsum⟩ := ih _ rfl
    subst hn
    refine ⟨Fin.append (fun _ : Fin (e a) => a) W, fun i => ?_, ?_⟩
    · induction i using Fin.addCases with
      | left k =>
        rw [Fin.append_left]
        exact Finset.mem_insert_self a s
      | right k =>
        rw [Fin.append_right]
        exact Finset.mem_insert_of_mem (hW k)
    · rw [Finset.sum_insert ha, ← hsum, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]

end PullbackEnum

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.exists_pullbackAlong_single_one_eq_sum
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : AlgebraicCurve.FundamentalIdentityAlong K
      φ hφ)
    (P : AlgebraicCurve.Place K F) (hdegP : P.deg = 1)
    (hdeg1 : ∀ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = P → w.deg = 1)
    (n : ℕ) (hn : AlgebraicCurve.finrankAlong K φ = n) :
    ∃ W : Fin n → AlgebraicCurve.Place K F',
      AlgebraicCurve.Divisor.pullbackAlong φ hφ (Finsupp.single P 1) = ∑ i, Finsupp.single (W i) 1 ∧
        ∀ i, (W i).restrictAlong φ hφ = P := by
  classical
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : FundamentalIdentity K F F' := hFI
  have hcount : ∑ w ∈ Place.fiberAlong φ hφ P, w.ramificationIndexAlong φ = n := by
    have h := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') P
    rw [hdegP, Nat.cast_one, mul_one] at h
    have h' : ∑ w ∈ P.fiber F', (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by
      rw [← h]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hdeg1 w (Place.mem_fiber.1 hw), Nat.cast_one, mul_one]
    have h'' : ((∑ w ∈ Place.fiberAlong φ hφ P, w.ramificationIndexAlong φ : ℕ) : ℤ) = (n : ℤ) := by
      rw [← hn]
      push_cast
      exact h'
    exact_mod_cast h''
  obtain ⟨W, hWmem, hWsum⟩ := PullbackEnum.exists_fin_sum_eq_sum_nsmul (Place.fiberAlong φ hφ P)
    (fun w => w.ramificationIndexAlong φ) (fun w => (Finsupp.single w (1 : ℤ) : Divisor K F')) n
      hcount
  refine ⟨W, ?_, fun i => Place.mem_fiberAlong.1 (hWmem i)⟩
  rw [Divisor.pullbackAlong_single, hWsum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [one_mul, Finsupp.smul_single, nsmul_eq_mul, mul_one]
end AlgebraicCurves.Divisors.Proofs.Divisor_exists_pullbackAlong_single_one_eq_sum
end ProofImplementation

end

section

/-!
# Divisor exists pullback Along single restrict Along eq single add sum of ramification
Index Along eq one
-/

section ProofImplementation

namespace AlgebraicCurve.Divisor

open _root_.AlgebraicCurve

theorem exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong
      K φ)
    (n : ℕ) (hn : finrankAlong K φ = n + 1)
    (hinert : ∀ W : Place K F', W.inertiaDegAlong φ hφ = 1)
    (W₀ : Place K F') (he : W₀.ramificationIndexAlong φ = 1) :
    ∃ (k : ℕ) (W : Fin k → Place K F') (e : Fin k → ℕ),
      (∀ j, 0 < e j) ∧ ∑ j, e j = n ∧ Function.Injective W ∧
      (∀ j, W j ≠ W₀) ∧ (∀ j, (W j).restrictAlong φ hφ = W₀.restrictAlong φ hφ) ∧
      (∀ W' : Place K F', W'.restrictAlong φ hφ = W₀.restrictAlong φ hφ → W' = W₀ ∨ ∃ j, W' = W j) ∧
      (∀ j, (W j).ramificationIndexAlong φ = e j) ∧
      Divisor.pullbackAlong φ hφ (Finsupp.single (W₀.restrictAlong φ hφ) 1) =
        Finsupp.single W₀ 1 + ∑ j, (e j : ℤ) • Finsupp.single (W j) 1 := by
  classical
  let := AlgebraicCurve.algebraAlong φ
  have := AlgebraicCurve.isScalarTower_along φ
  have := AlgebraicCurve.isIntegral_along φ hφ
  set w₀ := W₀.restrictAlong φ hφ with hw₀
  set S : Finset (Place K F') := (Place.fiberAlong φ hφ w₀).erase W₀ with hS
  have hW₀mem : W₀ ∈ Place.fiberAlong φ hφ w₀ := Place.mem_fiberAlong.mpr rfl
  let k := S.card
  let eq := S.equivFin
  let W : Fin k → Place K F' := fun j => (eq.symm j : Place K F')
  let e : Fin k → ℕ := fun j => (W j).ramificationIndexAlong φ
  have hWmem : ∀ j, W j ∈ S := fun j => (eq.symm j).2
  have hWinj : Function.Injective W := fun a b h => eq.symm.injective (Subtype.ext h)
  refine ⟨k, W, e, ?_, ?_, hWinj, ?_, ?_, ?_, fun j => rfl, ?_⟩
  · intro j
    change 0 < (W j).ramificationIndex F
    exact (W j).ramificationIndex_pos (F := F)
  · have hFI := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep w₀
    simp_rw [hinert, Nat.cast_one, mul_one] at hFI
    rw [hn, ← Finset.add_sum_erase _ _ hW₀mem] at hFI
    have he' : ((W₀.ramificationIndexAlong φ : ℕ) : ℤ) = 1 := by rw [he]; rfl
    rw [he'] at hFI
    have hsumS : ∑ w ∈ S, (w.ramificationIndexAlong φ : ℤ) = n := by
      push_cast at hFI; linarith
    have hre : ∑ j, (e j : ℤ) = ∑ w ∈ S, (w.ramificationIndexAlong φ : ℤ) := by
      rw [← Finset.sum_coe_sort S]
      exact Fintype.sum_equiv eq.symm _ _ (fun j => rfl)
    have : ((∑ j, e j : ℕ) : ℤ) = n := by push_cast; rw [hre, hsumS]
    exact_mod_cast this
  · intro j
    exact Finset.ne_of_mem_erase (hWmem j)
  · intro j
    exact Place.mem_fiberAlong.mp (Finset.mem_of_mem_erase (hWmem j))
  · intro W' hW'
    by_cases h : W' = W₀
    · exact Or.inl h
    · right
      have hmem : W' ∈ S := Finset.mem_erase.mpr ⟨h, Place.mem_fiberAlong.mpr hW'⟩
      exact ⟨eq ⟨W', hmem⟩,
        by change W' = ((eq.symm (eq ⟨W', hmem⟩)) : Place K F'); rw [Equiv.symm_apply_apply]⟩
  · change Divisor.pullback F' (Finsupp.single w₀ 1) = _
    rw [Divisor.pullback_single]
    change ∑ w ∈ Place.fiberAlong φ hφ w₀, Finsupp.single w (1 * (w.ramificationIndexAlong φ : ℤ))
      = _
    rw [← Finset.add_sum_erase _ _ hW₀mem]
    congr 1
    · rw [one_mul, show ((W₀.ramificationIndexAlong φ : ℕ) : ℤ) = 1 by rw [he]; rfl]
    · rw [← Finset.sum_coe_sort ((Place.fiberAlong φ hφ w₀).erase W₀)]
      refine (Fintype.sum_equiv eq.symm _ _ (fun j => ?_)).symm
      show (e j : ℤ) • Finsupp.single (W j) (1 : ℤ) = Finsupp.single _ _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one, one_mul]
end AlgebraicCurve.Divisor
end ProofImplementation

end
