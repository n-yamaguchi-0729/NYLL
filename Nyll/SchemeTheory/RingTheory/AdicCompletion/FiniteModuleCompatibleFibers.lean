/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModules
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
public import Nyll.SchemeTheory.RingTheory.LocalRing.MaximalIdealPowerQuotientLength
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Tactic.Abel

/-!
# Compatible fibers of maps from a finite complete local module

A compatible system of surjective maps from one finite module over a
complete Noetherian local ring is surjective on compatible sections,
provided the nth target is killed by the corresponding maximal-ideal
power. Equality of the map kernels with the adic powers is not required.

At each adic precision the images of the descending original kernels
stabilize in an Artinian quotient of the source. This supplies successive
approximations simultaneously compatible with every prescribed fiber.
Completeness supplies their limit, and target nilpotence identifies each
of its original evaluations. No simultaneous lift is supplied as data.
-/

@[expose] public section

noncomputable section

namespace AdicModuleSystem

universe u v w

/-- Every adic quotient of a finite module over a Noetherian local ring
is Artinian with its original scalar action. -/
theorem artinian_quotient_maximalPow_smul
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) :
    IsArtinian R (M ⧸ (IsLocalRing.maximalIdeal R ^ n • ⊤ : Submodule R M)) := by
  let J : Ideal R := IsLocalRing.maximalIdeal R ^ n
  let Q := M ⧸ (J • ⊤ : Submodule R M)
  have hart : IsArtinian R (R ⧸ J) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (EtaleFundamentalGroups.Purity.isFiniteLength_quotient_maximalIdeal_pow
        (R := R) n)).2
  have : IsArtinianRing (R ⧸ J) := isArtinian_of_tower R hart
  have : Module.Finite R Q :=
    Module.Finite.of_surjective (J • (⊤ : Submodule R M)).mkQ
      (Submodule.mkQ_surjective _)
  have : Module.Finite (R ⧸ J) Q := Module.Finite.of_restrictScalars_finite R (R ⧸ J) Q
  have : IsArtinian (R ⧸ J) Q := inferInstance
  exact isArtinian_of_surjective_algebraMap
    (R := R ⧸ J) (M := Q) (Ideal.Quotient.mk_surjective (I := J))

section Approximation

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  (N : ℕ → Type w) [∀ k : ℕ, AddCommGroup (N k)] [∀ k : ℕ, Module R (N k)]
  (t : ∀ k : ℕ, N (k + 1) →ₗ[R] N k)
  (f : ∀ k : ℕ, M →ₗ[R] N k)
  (hf : ∀ k : ℕ, (t k).comp (f (k + 1)) = f k)
  (hsurj : ∀ k : ℕ, Function.Surjective (f k))

include hf in
private theorem compatible_fibers_descend
    (z : sections N t) {a b : ℕ} (hab : a ≤ b) (x : M)
    (hx : f b x = z.val b) : f a x = z.val a := by
  revert hx
  induction b, hab using Nat.le_induction with
  | base => exact fun hx => hx
  | succ b _hab ih =>
      intro hx
      apply ih
      exact (LinearMap.congr_fun (hf b) x).symm.trans
        ((congrArg (t b) hx).trans (z.property b))

include hf hsurj in
private theorem exists_fiber_adic_approximation
    (hArt : ∀ n : ℕ, IsArtinian R (M ⧸ (I ^ n • ⊤ : Submodule R M)))
    (z : sections N t) (n : ℕ) :
    ∃ c : ℕ, ∀ x : M, f c x = z.val c →
      ∀ k : ℕ, ∃ y : M, f k y = z.val k ∧
        x - y ∈ (I ^ n • ⊤ : Submodule R M) := by
  let P : Submodule R M := I ^ n • ⊤
  let q : M →ₗ[R] M ⧸ P := P.mkQ
  have hker : Antitone (fun k : ℕ => (f k).ker) := by
    apply antitone_nat_of_succ_le
    intro k x hx
    change f k x = 0
    exact (LinearMap.congr_fun (hf k) x).symm.trans
      ((congrArg (t k) hx).trans (t k).map_zero)
  have : IsArtinian R (M ⧸ P) := hArt n
  let D : ℕ →o (Submodule R (M ⧸ P))ᵒᵈ :=
    { toFun := fun k => (f k).ker.map q
      monotone' := fun a b hab => Submodule.map_mono (hker hab) }
  obtain ⟨c, hc⟩ := IsArtinian.monotone_stabilizes D
  refine ⟨c, ?_⟩
  intro x hx k
  let b := max c k
  obtain ⟨y, hy⟩ := hsurj b (z.val b)
  have hyc : f c y = z.val c :=
    compatible_fibers_descend N t f hf z (le_max_left c k) y hy
  have hxy : x - y ∈ (f c).ker := by
    change f c (x - y) = 0
    rw [map_sub, hx, hyc, sub_self]
  have hD : (f c).ker.map q = (f b).ker.map q := hc b (le_max_left c k)
  have hmem : q (x - y) ∈ (f b).ker.map q := by
    rw [← hD]
    exact ⟨x - y, hxy, rfl⟩
  obtain ⟨w, hw, he⟩ := hmem
  refine ⟨y + w, ?_, ?_⟩
  · apply compatible_fibers_descend N t f hf z (le_max_right c k)
    change f b (y + w) = z.val b
    rw [map_add, hy, show f b w = 0 from hw, add_zero]
  · apply (Submodule.Quotient.mk_eq_zero P).mp
    change q (x - (y + w)) = 0
    rw [show x - (y + w) = (x - y) - w by abel, map_sub, ← he, sub_self]

variable [IsPrecomplete I M]

include hf hsurj in
/-- Artinian source quotients and completeness solve all compatible
original fibers. The only precision condition is that each original map
kills its specified adic power. -/
theorem exists_lift_of_artinian_quotients
    (hArt : ∀ n : ℕ, IsArtinian R (M ⧸ (I ^ n • ⊤ : Submodule R M)))
    (hkill : ∀ k : ℕ, (I ^ (k + 1) • ⊤ : Submodule R M) ≤ (f k).ker)
    (z : sections N t) : ∃ x : M, ∀ k : ℕ, f k x = z.val k := by
  let P : ℕ → Submodule R M := fun n => I ^ n • ⊤
  let good : ℕ → M → Prop := fun n x =>
    ∀ k : ℕ, ∃ y : M, f k y = z.val k ∧ x - y ∈ P n
  have hzero : good 0 0 := by
    intro k
    obtain ⟨y, hy⟩ := hsurj k (z.val k)
    refine ⟨y, hy, ?_⟩
    change (0 : M) - y ∈ (I ^ 0 • ⊤ : Submodule R M)
    rw [pow_zero, one_smul]
    exact Submodule.mem_top
  have hstep : ∀ n : ℕ, ∀ x : M, good n x →
      ∃ y : M, good (n + 1) y ∧ x - y ∈ P n := by
    intro n x hx
    obtain ⟨c, hc⟩ := exists_fiber_adic_approximation I N t f hf hsurj hArt z (n + 1)
    obtain ⟨y, hy, hxy⟩ := hx c
    exact ⟨y, hc y hy, hxy⟩
  let a : ∀ n : ℕ, {x : M // good n x} :=
    Nat.rec (motive := fun n : ℕ => {x : M // good n x}) ⟨0, hzero⟩
      (fun n x => ⟨(hstep n x.val x.property).choose,
        (hstep n x.val x.property).choose_spec.1⟩)
  have ha : ∀ n : ℕ, (a n).val - (a (n + 1)).val ∈ P n :=
    fun n => (hstep n (a n).val (a n).property).choose_spec.2
  let c : AdicCompletion.AdicCauchySequence I M := AdicCompletion.AdicCauchySequence.mk I M
    (fun n => (a n).val) (fun n => SModEq.sub_mem.mpr (ha n))
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I M)
    (f := fun n => (a n).val)
    (fun hab => c.property hab)
  refine ⟨x, ?_⟩
  intro k
  obtain ⟨y, hy, hay⟩ := (a (k + 1)).property k
  have hax : (a (k + 1)).val - x ∈ P (k + 1) := SModEq.sub_mem.mp (hx (k + 1))
  have hxy : x - y ∈ P (k + 1) := by
    have h := (P (k + 1)).sub_mem hay hax
    rw [show (a (k + 1)).val - y - ((a (k + 1)).val - x) = x - y by abel] at h
    exact h
  have hz : f k (x - y) = 0 := hkill k hxy
  exact (sub_eq_zero.mp (((f k).map_sub x y).symm.trans hz)).trans hy

end Approximation

/-- Compatible surjective maps from a finite module over a complete
Noetherian local ring lift every compatible family. The targets need
only be killed by their actual maximal-ideal powers; no equality of
transition kernels or source-map kernels is assumed. -/
theorem exists_lift_of_finite_completeLocal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : ℕ → Type w) [∀ k : ℕ, AddCommGroup (N k)] [∀ k : ℕ, Module R (N k)]
    (t : ∀ k : ℕ, N (k + 1) →ₗ[R] N k)
    (f : ∀ k : ℕ, M →ₗ[R] N k)
    (hf : ∀ k : ℕ, (t k).comp (f (k + 1)) = f k)
    (hsurj : ∀ k : ℕ, Function.Surjective (f k))
    (hpow : ∀ k : ℕ, (IsLocalRing.maximalIdeal R ^ (k + 1) •
      (⊤ : Submodule R (N k))) = ⊥)
    (z : sections N t) : ∃ x : M, ∀ k : ℕ, f k x = z.val k := by
  let I := IsLocalRing.maximalIdeal R
  have : IsAdicComplete I M := IsAdicComplete.of_module_finite I M
  have hkill : ∀ k : ℕ, (I ^ (k + 1) • ⊤ : Submodule R M) ≤ (f k).ker := by
    intro k x hx
    have hmem : f k x ∈ (I ^ (k + 1) • ⊤ : Submodule R (N k)) := by
      have hm : f k x ∈ Submodule.map (f k) (I ^ (k + 1) • ⊤ : Submodule R M) :=
        ⟨x, hx, rfl⟩
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr (hsurj k)] at hm
      exact hm
    rw [hpow k] at hmem
    exact hmem
  exact exists_lift_of_artinian_quotients I N t f hf hsurj
    (artinian_quotient_maximalPow_smul R M) hkill z

end AdicModuleSystem
