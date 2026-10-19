/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.SchemeTheory.RingTheory.Polynomial.Macaulay
import Nyll.AlgebraicCurves.Hilbert.LinearEquivBaseChangePieceMap
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialFinrankPieceSuccLeMacaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialEvalNeZeroMacaulayPowFinrankPieceSupAddLe
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomialEvalNeZeroMemMulMem

/-!
# Mv Polynomial finrank piece add two eq macaulay Pow of finrank piece succ eq macaulay Pow
-/

section ProofImplementation

open _root_.Nat.Macaulay

namespace AlgebraicCurves.Foundations.Polynomial.Proofs
namespace MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow

namespace GotzStep


open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

section Pieces

variable {L : Type} [Field L]

/-- The part of the ideal lying in the specified homogeneous component. -/
noncomputable def Ik (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Submodule L ↥(homogeneousSubmodule (Fin (n + 1)) L d) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) L d).subtype (I.restrictScalars L)

theorem mem_Ik {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (x : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) :
    x ∈ Ik I d ↔ (x : MvPolynomial (Fin (n + 1)) L) ∈ I := Iff.rfl

theorem Ik_mono {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} (h : I ≤ I') (d : ℕ) : Ik I d ≤ Ik I'
  d :=
  fun x hx => (mem_Ik x).mpr (h ((mem_Ik x).mp hx))

theorem piece_eq (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    piece I d = (↥(homogeneousSubmodule (Fin (n + 1)) L d) ⧸ Ik I d) := rfl

theorem finrank_piece_add (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Module.finrank L (piece I d) + Module.finrank L ↥(Ik I d) =
      Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  unfold Ik; exact Submodule.finrank_quotient_add_finrank _

theorem finrank_piece_eq_of_Ik_eq {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ} (h : Ik I d
  = Ik I' d) :
    Module.finrank L (piece I d) = Module.finrank L (piece I' d) := by
  unfold Ik at h; exact (Submodule.quotEquivOfEq _ _ h).finrank_eq

theorem finrank_piece_anti {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} (h : I ≤ I') (d : ℕ) :
    Module.finrank L (piece I' d) ≤ Module.finrank L (piece I d) := by
  have h1 := finrank_piece_add I d
  have h2 := finrank_piece_add I' d
  have h3 : Module.finrank L ↥(Ik I d) ≤ Module.finrank L ↥(Ik I' d) := Submodule.finrank_mono
    (Ik_mono h d)
  omega

theorem finrank_piece_eq_zero_of_forall {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (h : ∀ f : MvPolynomial (Fin (n + 1)) L, f.IsHomogeneous d → f ∈ I) : Module.finrank L (piece I
      d) = 0 := by
  have htop : Ik I d = ⊤ := eq_top_iff.mpr fun x _ => (mem_Ik x).mpr (h x x.2)
  have h1 := finrank_piece_add I d
  rw [htop, finrank_top] at h1
  omega

theorem mem_of_finrank_piece_eq_zero {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (h : Module.finrank L (piece I d) = 0) (f : MvPolynomial (Fin (n + 1)) L) (hf : f.IsHomogeneous
      d) :
    f ∈ I := by
  have h1 := finrank_piece_add I d
  rw [h, zero_add] at h1
  have htop : Ik I d = ⊤ := Submodule.eq_top_of_finrank_eq h1
  have : (⟨f, hf⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) ∈ Ik I d := by rw [htop]; trivial
  exact (mem_Ik _).mp this

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) L) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) L) q d : MvPolynomial (Fin (n + 1)) L)
      =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mul_add {G : MvPolynomial (Fin (n + 1)) L} {m : ℕ} (hG :
  G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) L) (d : ℕ) :
    homogeneousComponent (m + d) (a * G) = homogeneousComponent d a * G := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) L)
    (a := a) (show G ∈ homogeneousSubmodule (Fin (n + 1)) L m from hG) (Nat.le_add_right m d)
  rw [decompose_eq, decompose_eq, Nat.add_sub_cancel_left] at this
  exact this

theorem span_homogeneous (s : Set (MvPolynomial (Fin (n + 1)) L))
    (hs : ∀ p ∈ s, ∃ i : ℕ, p.IsHomogeneous i) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) L) s (fun x hx => hs x hx)
  have := H d hp
  rwa [decompose_eq] at this

theorem finrank_piece_succ_eq_add (I : Ideal (MvPolynomial (Fin (n + 1)) L))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (ℓ : MvPolynomial (Fin (n + 1)) L) (hℓ : ℓ.IsHomogeneous 1) (k : ℕ)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) L, f.IsHomogeneous k → ℓ * f ∈ I → f ∈ I) :
    Module.finrank L (piece I (k + 1)) =
      Module.finrank L (piece I k) + Module.finrank L (piece (I ⊔ Ideal.span {ℓ}) (k + 1)) := by
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have h0 : Module.finrank L (piece I k) = 0 :=
      finrank_piece_eq_zero_of_forall fun f hf => hcol f hf (by rw [zero_mul]; exact I.zero_mem)
    have hbot : Ideal.span ({0} : Set (MvPolynomial (Fin (n + 1)) L)) = ⊥ :=
      Ideal.span_singleton_eq_bot.mpr rfl
    rw [h0, zero_add, hbot, sup_bot_eq]
  let μ : ↥(homogeneousSubmodule (Fin (n + 1)) L k) →ₗ[L] ↥(homogeneousSubmodule (Fin (n + 1)) L (k
    + 1)) :=
    LinearMap.codRestrict (homogeneousSubmodule (Fin (n + 1)) L (k + 1))
      ((LinearMap.mulLeft L ℓ) ∘ₗ (homogeneousSubmodule (Fin (n + 1)) L k).subtype)
      (fun f => by
        change (ℓ * (f : MvPolynomial (Fin (n + 1)) L)).IsHomogeneous (k + 1)
        have := hℓ.mul f.2; rwa [Nat.add_comm 1 k] at this)
  have hμ : ∀ f : ↥(homogeneousSubmodule (Fin (n + 1)) L k),
      (μ f : MvPolynomial (Fin (n + 1)) L) = ℓ * f := fun f => rfl
  have hμinj : Function.Injective μ := by
    intro f g hfg
    have := congrArg Subtype.val hfg
    rw [hμ, hμ] at this
    exact Subtype.ext (mul_left_cancel₀ hℓ0 this)
  have hA1 : Ik (I ⊔ Ideal.span {ℓ}) (k + 1) = Ik I (k + 1) ⊔ LinearMap.range μ := by
    apply le_antisymm
    · intro x hx
      rw [mem_Ik] at hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      have hx1 : (x : MvPolynomial (Fin (n + 1)) L) = homogeneousComponent (k + 1) x := by
        rw [homogeneousComponent_of_mem x.2, ite_eq_left rfl]
      have hgl : homogeneousComponent (k + 1) (g * ℓ) = homogeneousComponent k g * ℓ := by
        rw [Nat.add_comm k 1]; exact homogeneousComponent_mul_add hℓ g k
      have hyk : homogeneousComponent (k + 1) y ∈ homogeneousSubmodule (Fin (n + 1)) L (k + 1) :=
        homogeneousComponent_isHomogeneous _ _
      have hgk : homogeneousComponent k g ∈ homogeneousSubmodule (Fin (n + 1)) L k :=
        homogeneousComponent_isHomogeneous _ _
      have hxeq : (x : MvPolynomial (Fin (n + 1)) L) =
          homogeneousComponent (k + 1) y + ℓ * homogeneousComponent k g := by
        calc (x : MvPolynomial (Fin (n + 1)) L) = homogeneousComponent (k + 1) (y + g * ℓ) := by
              rw [hyz]; exact hx1
          _ = homogeneousComponent (k + 1) y + ℓ * homogeneousComponent k g := by
              rw [map_add, hgl, mul_comm ℓ]
      have hxeq' : x = ⟨homogeneousComponent (k + 1) y, hyk⟩ + μ ⟨homogeneousComponent k g, hgk⟩ :=
        by
        apply Subtype.ext
        rw [Submodule.coe_add, hμ]
        exact hxeq
      rw [hxeq']
      exact Submodule.add_mem_sup ((mem_Ik _).mpr (hI y hy (k + 1))) (LinearMap.mem_range_self μ _)
    · apply sup_le (Ik_mono (I := I) (I' := I ⊔ Ideal.span {ℓ}) le_sup_left (k + 1))
      rintro _ ⟨f, rfl⟩
      rw [mem_Ik, hμ]
      exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ℓ))
  have hA2 : Ik I (k + 1) ⊓ LinearMap.range μ = (Ik I k).map μ := by
    apply le_antisymm
    · rintro y ⟨hyI, ⟨f, rfl⟩⟩
      have hyI' : ℓ * (f : MvPolynomial (Fin (n + 1)) L) ∈ I :=
        by rw [← hμ]; exact (mem_Ik _).mp hyI
      have hf : f ∈ Ik I k := (mem_Ik f).mpr (hcol f f.2 hyI')
      exact Submodule.mem_map_of_mem hf
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨(mem_Ik _).mpr ?_, LinearMap.mem_range_self μ f⟩
      rw [hμ]; exact I.mul_mem_left ℓ ((mem_Ik f).mp hf)
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Ik I (k + 1)) (LinearMap.range μ)
  rw [← hA1, hA2, LinearMap.finrank_range_of_inj hμinj,
    (Submodule.equivMapOfInjective μ hμinj (Ik I k)).symm.finrank_eq] at e1
  have e2 := finrank_piece_add I k
  have e3 := finrank_piece_add I (k + 1)
  have e4 := finrank_piece_add (I ⊔ Ideal.span {ℓ}) (k + 1)
  omega

end Pieces

section Regen

variable {L : Type} [Field L]

theorem exists_eq_sum_X_mul (k : ℕ) (g : MvPolynomial (Fin (n + 1)) L) (hg : g.IsHomogeneous (k +
  1)) :
    ∃ q : Fin (n + 1) → MvPolynomial (Fin (n + 1)) L, (∀ i, (q i).IsHomogeneous k) ∧ g = ∑ i, X i *
      q i := by
  classical
  have hg' : g ∈ (Submodule.span L ((fun μ : Fin (n + 1) →₀ ℕ => monomial μ (1 : L)) ''
      {μ : Fin (n + 1) →₀ ℕ | μ.degree = k + 1}) : Submodule L (MvPolynomial (Fin (n + 1)) L)) := by
    have : g ∈ homogeneousSubmodule (Fin (n + 1)) L (k + 1) := hg
    rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single]
      at this
    exact this
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨μ, hμ, rfl⟩ := hx
      have hμ' : μ.degree = k + 1 := hμ
      have hne : μ ≠ 0 := by rintro rfl; rw [map_zero] at hμ'; omega
      obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
        by_contra h; push Not at h; exact hne (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ μ := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
      have hdeg : (μ - Finsupp.single i 1).degree = k := by
        have h1 : μ - Finsupp.single i 1 + Finsupp.single i 1 = μ := tsub_add_cancel_of_le hle
        have h2 := congrArg Finsupp.degree h1
        rw [map_add, Finsupp.degree_single, hμ'] at h2
        omega
      refine ⟨Pi.single i (monomial (μ - Finsupp.single i 1) 1), fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same]; exact isHomogeneous_monomial _ hdeg
        · rw [Pi.single_eq_of_ne hj]; exact isHomogeneous_zero _ _ _
      · rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same]
        change (monomial μ (1 : L)) = monomial (Finsupp.single i 1) 1 * monomial (μ -
          Finsupp.single i 1) 1
        rw [monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle]
  | zero => exact ⟨0, fun _ => isHomogeneous_zero _ _ _, by
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]⟩
  | add x y _ _ hx hy =>
      obtain ⟨q₁, hq₁, rfl⟩ := hx
      obtain ⟨q₂, hq₂, rfl⟩ := hy
      exact ⟨q₁ + q₂, fun i => (hq₁ i).add (hq₂ i), by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ =>
          by rw [Pi.add_apply, mul_add]⟩
  | smul c x _ hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      refine ⟨fun i => C c * q i, fun i => (hq i).C_mul c, ?_⟩
      rw [smul_eq_C_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm]

theorem finrank_piece_succ_eq_zero {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {k : ℕ}
    (h : Module.finrank L (piece I k) = 0) : Module.finrank L (piece I (k + 1)) = 0 := by
  apply finrank_piece_eq_zero_of_forall
  intro g hg
  obtain ⟨q, hq, rfl⟩ := exists_eq_sum_X_mul k g hg
  exact I.sum_mem fun i _ => I.mul_mem_left _ (mem_of_finrank_piece_eq_zero h (q i) (hq i))

variable {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) L))
  (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
  (ℓ : MvPolynomial (Fin (n + 1)) L) (hℓ : ℓ.IsHomogeneous 1)

include hJ in
theorem homogeneous_of_gen : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  exact span_homogeneous s fun p hp => ⟨m, hs p hp⟩
include hJ hℓ in
theorem homogeneous_sup : ∀ p ∈ J ⊔ Ideal.span {ℓ}, ∀ i : ℕ, homogeneousComponent i p ∈ J ⊔
  Ideal.span {ℓ} := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have : Ideal.span s ⊔ Ideal.span {ℓ} = Ideal.span (s ∪ {ℓ}) := (Submodule.span_union s {ℓ}).symm
  rw [this]
  refine span_homogeneous (s ∪ {ℓ}) ?_
  rintro p (hp | hp)
  · exact ⟨m, hs p hp⟩
  · exact ⟨1, by rw [Set.mem_singleton_iff.mp hp]; exact hℓ⟩

/-- The ideal generated by homogeneous forms of the fixed degree after adjoining the linear
form. -/
noncomputable def regen (m : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) L)) (ℓ : MvPolynomial (Fin
  (n + 1)) L) :
    Ideal (MvPolynomial (Fin (n + 1)) L) :=
  Ideal.span {p | p ∈ J ⊔ Ideal.span {ℓ} ∧ p.IsHomogeneous m}

theorem regen_le : regen m J ℓ ≤ J ⊔ Ideal.span {ℓ} := Ideal.span_le.mpr fun _ hp => hp.1

theorem regen_generated : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧
    regen m J ℓ = Ideal.span s := ⟨_, fun _ hp => hp.2, rfl⟩
include hJ in
theorem le_regen : J ≤ regen m J ℓ := by
  obtain ⟨s, hs, rfl⟩ := hJ
  exact Ideal.span_le.mpr fun p hp => Ideal.subset_span ⟨Ideal.mem_sup_left (Ideal.subset_span hp),
    hs p hp⟩
include hJ hℓ in
theorem mem_regen_of_mem (hm : 1 ≤ m) : ∀ (j : ℕ) (x : MvPolynomial (Fin (n + 1)) L),
    x.IsHomogeneous (m + j) → x ∈ J ⊔ Ideal.span {ℓ} → x ∈ regen m J ℓ
  | 0, x, hx, hxI => Ideal.subset_span ⟨hxI, hx⟩
  | j + 1, x, hx, hxI => by
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxI
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      have hx1 : x = homogeneousComponent (m + j + 1) x := by
        rw [homogeneousComponent_of_mem (show x ∈ homogeneousSubmodule (Fin (n + 1)) L (m + j + 1)
          from hx),
          ite_eq_left rfl]
      have hgl : homogeneousComponent (m + j + 1) (g * ℓ) = homogeneousComponent (m + j) g * ℓ := by
        rw [Nat.add_comm (m + j) 1]; exact homogeneousComponent_mul_add hℓ g (m + j)
      rw [hx1, ← hyz, map_add, hgl]
      refine Ideal.add_mem _ (le_regen J hJ ℓ (homogeneous_of_gen J hJ y hy _)) ?_
      have hmj : m + j = (m + j - 1) + 1 := by omega
      obtain ⟨q, hq, hgq⟩ := exists_eq_sum_X_mul (m + j - 1) (homogeneousComponent (m + j) g)
        (by rw [← hmj]; exact homogeneousComponent_isHomogeneous _ _)
      rw [hgq, Finset.sum_mul]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [mul_assoc]
      refine Ideal.mul_mem_left _ _ (mem_regen_of_mem hm j (q i * ℓ) ?_ ?_)
      · have := (hq i).mul hℓ; rwa [← hmj] at this
      · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self ℓ))
include hJ hℓ in
theorem Ik_regen_eq (hm : 1 ≤ m) {k : ℕ} (hk : m ≤ k) : Ik (regen m J ℓ) k = Ik (J ⊔ Ideal.span
  {ℓ}) k := by
  apply le_antisymm (Ik_mono (regen_le J ℓ) k)
  intro x hx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (mem_Ik x).mpr (mem_regen_of_mem J hJ ℓ hℓ hm j x x.2 ((mem_Ik x).mp hx))

end Regen

section BaseChange

variable (K L : Type) [Field K] [Field L] [Algebra K L]

theorem finrank_piece_map (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) (d : ℕ) :
    Module.finrank L (piece (J.map (MvPolynomial.map (algebraMap K L))) d) = Module.finrank K
      (piece J d) := by
  obtain ⟨-, h⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n K L J
    hJ
  obtain ⟨e, -⟩ := h d
  rw [← e.finrank_eq, Module.finrank_baseChange]

theorem map_generated {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span
      s) :
    ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧
      J.map (MvPolynomial.map (algebraMap K L)) = Ideal.span s := by
  obtain ⟨s, hs, rfl⟩ := hJ
  refine ⟨MvPolynomial.map (algebraMap K L) '' s, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (hs p hp).map _

end BaseChange

section Core

variable {L : Type} [Field L]

theorem isHomogeneous_linearForm (a : Fin (n + 1) → L) :
    (∑ i, C (a i) * X i : MvPolynomial (Fin (n + 1)) L).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (a i) i

variable [Infinite L]

theorem exists_eval_ne_zero {G₁ G₂ : MvPolynomial (Fin (n + 1)) L} (h₁ : G₁ ≠ 0) (h₂ : G₂ ≠ 0) :
    ∃ a : Fin (n + 1) → L, MvPolynomial.eval a G₁ ≠ 0 ∧ MvPolynomial.eval a G₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply mul_ne_zero h₁ h₂
  apply MvPolynomial.funext
  intro a
  rw [map_mul, map_zero]
  by_cases h1 : MvPolynomial.eval a G₁ = 0
  · rw [h1, zero_mul]
  · rw [hcon a h1, mul_zero]

theorem core {m : ℕ} (hm : 1 ≤ m) : ∀ (N : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) L)),
    (∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s) →
    Module.finrank L (piece J m) ≤ N →
    Module.finrank L (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank L (piece J m)) →
    Module.finrank L (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank L (piece J (m +
      1))) := by
  intro N
  induction N with
  | zero =>
      intro J _ hN hmax
      have h0 : Module.finrank L (piece J m) = 0 := Nat.le_zero.mp hN
      rw [h0, Nat.Macaulay.macaulayPow_zero_right] at hmax
      rw [hmax, finrank_piece_succ_eq_zero hmax, Nat.Macaulay.macaulayPow_zero_right]
  | succ N ih =>
      intro J hJ hN hmax
      by_cases hs : Module.finrank L (piece J m) ≤ N
      · exact ih J hJ hs hmax
      have hs0 : 0 < Module.finrank L (piece J m) := by omega
      have hJh := homogeneous_of_gen J hJ
      obtain ⟨G₁, hG₁, H₁⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le n m hm L J hJh
      obtain ⟨G₂, hG₂, H₂⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
          n m L J hJ hmax
      obtain ⟨a, ha₁, ha₂⟩ := exists_eval_ne_zero hG₁ hG₂
      have hrt := H₁ a ha₁
      have hcol := H₂ a ha₂
      set ℓ : MvPolynomial (Fin (n + 1)) L := ∑ i, C (a i) * X i with hℓdef
      have hℓ : ℓ.IsHomogeneous 1 := isHomogeneous_linearForm a
      have hJ'h := homogeneous_sup J hJ ℓ hℓ
      have hA := finrank_piece_succ_eq_add J hJh ℓ hℓ m (fun f hf h => hcol m le_rfl f hf h)
      have hB := finrank_piece_succ_eq_add J hJh ℓ hℓ (m + 1) (fun f hf h => hcol (m + 1)
        (Nat.le_succ m) f hf h)
      have hmac := MvPolynomial.finrank_piece_succ_le_macaulayPow n m hm L (J ⊔ Ideal.span {ℓ}) hJ'h
      have hreg : ∀ k, m ≤ k →
          Module.finrank L (piece (regen m J ℓ) k) = Module.finrank L (piece (J ⊔ Ideal.span {ℓ})
            k) :=
        fun k hk => finrank_piece_eq_of_Ik_eq (Ik_regen_eq J hJ ℓ hℓ hm hk)
      set s0 := Module.finrank L (piece J m) with hs0def
      set s1 := Module.finrank L (piece J (m + 1)) with hs1def
      set s2 := Module.finrank L (piece J (m + 2)) with hs2def
      set t0 := Module.finrank L (piece (J ⊔ Ideal.span {ℓ}) m) with ht0def
      set t1 := Module.finrank L (piece (J ⊔ Ideal.span {ℓ}) (m + 1)) with ht1def
      set t2 := Module.finrank L (piece (J ⊔ Ideal.span {ℓ}) (m + 2)) with ht2def
      have ht1 : t1 = Nat.macaulayPow m t0 := by omega
      have hlt : t0 < s0 := Nat.Macaulay.lt_of_macaulayPow_add_le hrt hs0
      have ihr := ih (regen m J ℓ) (regen_generated J ℓ) (by rw [hreg m le_rfl]; omega)
        (by rw [hreg m le_rfl, hreg (m + 1) (Nat.le_succ m)]; exact ht1)
      rw [hreg (m + 1) (Nat.le_succ m), hreg (m + 2) (by omega), ← ht1def, ← ht2def] at ihr
      have key := Nat.Macaulay.macaulayPow_macaulayPow m s0
      have ht1' : t1 = Nat.macaulayPow m s0 - s0 := by omega
      rw [hB, ihr, ht1', hmax, key]

end Core

theorem main (n m : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    Module.finrank K (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank K (piece J (m +
      1))) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · change Module.finrank K (piece J 1) = Nat.macaulayPow 0 (Module.finrank K (piece J 0)) at hmax
    change Module.finrank K (piece J 2) = Nat.macaulayPow 1 (Module.finrank K (piece J 1))
    rw [Nat.Macaulay.macaulayPow_zero] at hmax
    have h2 : Module.finrank K (piece J 2) = 0 := finrank_piece_succ_eq_zero hmax
    rw [hmax, h2, Nat.Macaulay.macaulayPow_zero_right]
  · have hJh := homogeneous_of_gen J hJ
    have e := finrank_piece_map K (AlgebraicClosure K) J hJh
    have h := core hm (Module.finrank (AlgebraicClosure K)
        (piece (J.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) m))
      (J.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) (map_generated K
        (AlgebraicClosure K) J hJ)
      le_rfl (by rw [e, e]; exact hmax)
    rw [e, e] at h
    exact h

end GotzStep



open MvPolynomial AlgebraicGeometry.HilbertFunctor in
theorem
  _root_.MvPolynomial.finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    Module.finrank K (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank K (piece J (m +
      1))) :=
  GotzStep.main n m K J hJ hmax
end MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
end AlgebraicCurves.Foundations.Polynomial.Proofs
end ProofImplementation
