/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_finrank_piece_succ_le_macaulayPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Batteries.Tactic.Init
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.RelClasses
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.SchemeTheory.RingTheory.Polynomial.Macaulay
import Nyll.AlgebraicCurves.Foundations.Polynomial.MacaulayMonomials
import Nyll.SchemeTheory.RingTheory.Polynomial.FinsuppCardLeMacaulayPowCard

/-!
# Mv Polynomial finrank piece succ le macaulay Pow
-/

section ProofImplementation

open _root_.Nat.Macaulay _root_.MvPolynomial.Macaulay

namespace AlgebraicCurves.Foundations.Polynomial.Proofs
namespace MvPolynomial_finrank_piece_succ_le_macaulayPow

namespace MacaulayRed

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped MonomialOrder

variable (n : ℕ)

private noncomputable def _root_.MacaulayRed.lex : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
export _root_.MacaulayRed (lex)

variable (K : Type) [Field K]

/-- The leading exponent vectors of nonzero homogeneous elements of the ideal. -/
noncomputable def LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ)
  := by
  classical
  exact (Mon n e).filter fun a => ∃ f : MvPolynomial (Fin (n + 1)) K,
    f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a

theorem mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) (a : Fin (n + 1) →₀ ℕ) :
    a ∈ LM n K J e ↔ a.degree = e ∧ ∃ f : MvPolynomial (Fin (n + 1)) K,
      f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a := by
  classical
  simp [LM]

theorem LM_subset (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) : LM n K J e ⊆ Mon n e := by
  classical
  intro a ha; unfold LM at ha; exact (Finset.mem_filter.1 ha).1

theorem degree_mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    {f : MvPolynomial (Fin (n + 1)) K} (hfJ : f ∈ J) (hf : f.IsHomogeneous e) (hf0 : f ≠ 0) :
    (lex n).degree f ∈ LM n K J e := by
  rw [mem_LM]
  exact ⟨degree_eq_of_mem_support n K hf ((lex n).degree_mem_support hf0), f, hfJ, hf, hf0, rfl⟩

theorem add_single_mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (d : ℕ)
    {a : Fin (n + 1) →₀ ℕ} (ha : a ∈ LM n K J d) (i : Fin (n + 1)) :
    a + Finsupp.single i 1 ∈ LM n K J (d + 1) := by
  rw [mem_LM] at ha
  obtain ⟨-, f, hfJ, hf, hf0, hfa⟩ := ha
  have h1 : f * X i ∈ J := Ideal.mul_mem_right _ _ hfJ
  have h2 : (f * X i).IsHomogeneous (d + 1) := hf.mul (isHomogeneous_X K i)
  have h3 : f * X i ≠ 0 := mul_ne_zero hf0 (X_ne_zero i)
  have h4 : (lex n).degree (f * X i) = a + Finsupp.single i 1 := by
    rw [MonomialOrder.degree_mul hf0 (X_ne_zero i), MonomialOrder.degree_X, hfa]
  rw [← h4]
  exact degree_mem_LM n K J (d + 1) h1 h2 h3

/-- The part of the ideal lying in the specified homogeneous component. -/
noncomputable def W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Submodule K ↥(homogeneousSubmodule (Fin (n + 1)) K e) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K e).subtype (J.restrictScalars K)

theorem mem_W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    (p : ↥(homogeneousSubmodule (Fin (n + 1)) K e)) : p ∈ W n K J e ↔ (p : MvPolynomial _ K) ∈ J :=
  Iff.rfl

theorem finrank_homogeneousSubmodule (e : ℕ) :
    Module.finrank K ↥(homogeneousSubmodule (Fin (n + 1)) K e) = (Mon n e).card := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  refine (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {x : Fin (n + 1) →₀ ℕ | x.degree = e})).trans ?_
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _
    ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
      (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm))]
  rfl

theorem finrank_W_le (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K ↥(W n K J e) ≤ (LM n K J e).card := by
  classical
  let ψ : ↥(W n K J e) →ₗ[K] (↥(LM n K J e) → K) :=
    LinearMap.pi fun a =>
      ((lcoeff K a.1).comp (homogeneousSubmodule (Fin (n + 1)) K e).subtype).comp
        (W n K J e).subtype
  have hker : LinearMap.ker ψ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
    rw [LinearMap.mem_ker] at hp
    by_contra hp0
    have hf0 : (p.1 : MvPolynomial (Fin (n + 1)) K) ≠ 0 := by
      intro h; apply hp0
      exact Subtype.ext (Subtype.ext h)
    have hmem := degree_mem_LM n K J e ((mem_W n K J e p.1).1 p.2) p.1.2 hf0
    have := congrFun hp ⟨_, hmem⟩
    rw [Pi.zero_apply] at this
    change (p.1 : MvPolynomial (Fin (n + 1)) K).coeff
      ((lex n).degree (p.1 : MvPolynomial (Fin (n + 1)) K)) = 0 at this
    exact ((lex n).leadingCoeff_ne_zero_iff.2 hf0) this
  have hψ : Function.Injective ψ :=
    (LinearMap.ker_eq_bot (M := ↥(W n K J e)) (M₂ := (↥(LM n K J e) → K)) (f := ψ)).1 hker
  have := LinearMap.finrank_le_finrank_of_injective hψ
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this

theorem linearIndependent_of_degree_eq (s : Finset (Fin (n + 1) →₀ ℕ))
    (g : ↥s → MvPolynomial (Fin (n + 1)) K) (hg0 : ∀ a, g a ≠ 0)
    (hg : ∀ a, (lex n).degree (g a) = a.1) : LinearIndependent K g := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  set t : Finset ↥s := Finset.univ.filter fun a => c a ≠ 0 with ht
  have htne : t.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, by simp [ht, ha]⟩
  obtain ⟨a₀, ha₀, hmax⟩ := t.exists_max_image (fun a => (lex n).toSyn a.1) htne
  have hca₀ : c a₀ ≠ 0 := by simpa [ht] using ha₀
  have hcoeff : (∑ a, c a • g a).coeff a₀.1 = c a₀ * (lex n).leadingCoeff (g a₀) := by
    rw [coeff_sum, Finset.sum_eq_single a₀]
    · rw [coeff_smul, smul_eq_mul, MonomialOrder.leadingCoeff, hg a₀]
    · intro a _ haa
      by_cases hca : c a = 0
      · simp [hca]
      · have hle : (lex n).toSyn a.1 ≤ (lex n).toSyn a₀.1 := hmax a (by simp [ht, hca])
        have hlt : (lex n).toSyn a.1 < (lex n).toSyn a₀.1 := by
          refine lt_of_le_of_ne hle fun h => haa ?_
          exact Subtype.ext ((lex n).toSyn.injective h)
        rw [coeff_smul, (lex n).coeff_eq_zero_of_lt (by rw [hg a]; exact hlt), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc, AddMonoidAlgebra.coeff_zero] at hcoeff
  exact mul_ne_zero hca₀ ((lex n).leadingCoeff_ne_zero_iff.2 (hg0 a₀)) hcoeff.symm

theorem card_LM_le (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    (LM n K J e).card ≤ Module.finrank K ↥(W n K J e) := by
  classical
  have hex : ∀ a : ↥(LM n K J e), ∃ f : MvPolynomial (Fin (n + 1)) K,
      f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a.1 := fun a =>
    ((mem_LM n K J e a.1).1 a.2).2
  choose f hfJ hfh hf0 hfd using hex
  let g : ↥(LM n K J e) → ↥(W n K J e) := fun a => ⟨⟨f a, hfh a⟩, (mem_W n K J e _).2 (hfJ a)⟩
  have hli : LinearIndependent K g := by
    apply LinearIndependent.of_comp
      ((homogeneousSubmodule (Fin (n + 1)) K e).subtype.comp (W n K J e).subtype)
    exact linearIndependent_of_degree_eq n K _ (fun a => f a) hf0 hfd
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_coe] at this

theorem finrank_W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K ↥(W n K J e) = (LM n K J e).card :=
  le_antisymm (finrank_W_le n K J e) (card_LM_le n K J e)

theorem finrank_piece_add (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K (piece J e) + (LM n K J e).card = (Mon n e).card := by
  rw [← finrank_W n K J e, ← finrank_homogeneousSubmodule n K e]
  exact Submodule.finrank_quotient_add_finrank (W n K J e)

end MacaulayRed

attribute [local simp] MvPolynomial.Macaulay.mem_Mon


open _root_.AlgebraicCurves.Foundations.Polynomial.Proofs in
open MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed in
open MvPolynomial AlgebraicGeometry.HilbertFunctor in
theorem _root_.MvPolynomial.finrank_piece_succ_le_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (_hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) := by
  classical
  set B : Finset (Fin (n + 1) →₀ ℕ) := Mon n d \ LM n K J d with hB
  set C : Finset (Fin (n + 1) →₀ ℕ) := Mon n (d + 1) \ LM n K J (d + 1) with hC
  have hBcard : B.card + (LM n K J d).card = (Mon n d).card := by
    rw [hB, Finset.card_sdiff_add_card_eq_card (LM_subset n K J d)]
  have hCcard : C.card + (LM n K J (d + 1)).card = (Mon n (d + 1)).card := by
    rw [hC, Finset.card_sdiff_add_card_eq_card (LM_subset n K J (d + 1))]
  have hd₀ := finrank_piece_add n K J d
  have hd₁ := finrank_piece_add n K J (d + 1)
  have h1 : Module.finrank K (piece J (d + 1)) = C.card := by omega
  have h2 : Module.finrank K (piece J d) = B.card := by omega
  rw [h1, h2]
  refine Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem n d hd B
    (fun m hm => (mem_Mon n d m).1 (Finset.mem_sdiff.1 hm).1) C
    (fun u hu => (mem_Mon n (d + 1) u).1 (Finset.mem_sdiff.1 hu).1) fun u hu i hi => ?_
  obtain ⟨hu, huA⟩ := Finset.mem_sdiff.1 hu
  rw [mem_Mon] at hu
  refine Finset.mem_sdiff.2 ⟨(mem_Mon n d _).2 ?_, fun hA => huA ?_⟩
  · have h := Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)
    have := congrArg Finsupp.degree h
    rw [map_add, Finsupp.degree_single, hu] at this
    omega
  · have := add_single_mem_LM n K J d hA i
    rwa [Finsupp.sub_add_single_one_cancel (by omega)] at this
end AlgebraicCurves.Foundations.Polynomial.Proofs.MvPolynomial_finrank_piece_succ_le_macaulayPow
end ProofImplementation
