/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModules
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.LinearAlgebra.SModEq.Pow
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.Abel

/-!
# Effectivity of finite adic module systems

The module constructed here is the submodule of compatible sequences in a
system of finite modules. Surjective transition maps and their actual adic
kernels allow a finite presentation at the first level to be corrected one
power of the ideal at a time. Completeness then gives a surjection from a
finite free module to the compatible-sequence module. The same construction
with a prescribed initial approximation computes every projection kernel.

The hypotheses on the transition kernels express that the supplied system
is obtained by reduction from each successive level. They do not assume an
effective module or a comparison with its reductions. Both are constructed.
This is the affine module step needed before effectivity of formal coherent
sheaves; it does not assert Grothendieck existence on a proper scheme.

Background: https://stacks.math.columbia.edu/tag/00M9.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w

variable {R : Type u} [CommRing R]
  (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (t : (n : ℕ) → M (n + 1) →ₗ[R] M n)

/-- The actual module of compatible sequences of the given system. -/
def sections : Submodule R ((n : ℕ) → M n) where
  carrier := { x : (n : ℕ) → M n | ∀ n : ℕ, t n (x (n + 1)) = x n }
  zero_mem' := by
    intro n
    exact (t n).map_zero
  add_mem' := by
    intro x y hx hy n
    change t n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' := by
    intro a x hx n
    change t n (a • x (n + 1)) = a • x n
    rw [map_smul, hx n]

/-- Projection from the constructed module to a finite level. -/
def eval (n : ℕ) : sections M t →ₗ[R] M n :=
  (LinearMap.proj n).comp (sections M t).subtype

theorem eval_apply (n : ℕ) (x : sections M t) : eval M t n x = x.val n := rfl

theorem transition_eval (n : ℕ) (x : sections M t) :
    t n (eval M t (n + 1) x) = eval M t n x :=
  x.property n

/-- Agreement at a later level implies agreement at every earlier level. -/
theorem eval_eq_of_le {n m : ℕ} (hnm : n ≤ m) (x y : sections M t)
    (hxy : eval M t m x = eval M t m y) : eval M t n x = eval M t n y := by
  revert hxy
  induction m, hnm using Nat.le_induction with
  | base => exact fun h : eval M t n x = eval M t n y => h
  | succ m _hnm ih =>
      intro h
      apply ih
      exact (transition_eval M t m x).symm.trans
        ((congrArg (t m) h).trans (transition_eval M t m y))

/-- Surjective transition maps extend every first-level element to an
actual compatible sequence. -/
theorem eval_zero_surjective (ht : ∀ n : ℕ, Function.Surjective (t n)) :
    Function.Surjective (eval M t 0) := by
  intro x
  let s : (n : ℕ) → M n :=
    Nat.rec (motive := fun n : ℕ => M n) x
      (fun n y => (ht n y).choose)
  have hs : ∀ n : ℕ, t n (s (n + 1)) = s n :=
    fun n => (ht n (s n)).choose_spec
  exact ⟨⟨s, hs⟩, rfl⟩

variable (I : Ideal R)

section Approximation

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- An approximation at any prescribed finite level lifts to a compatible
sequence without changing that approximation. The lift is obtained by an
explicit sequence of corrections in successive ideal powers. -/
theorem exists_lift_with_congruence [IsPrecomplete I N]
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (F : N →ₗ[R] sections M t)
    (hF : ∀ n : ℕ, Function.Surjective ((eval M t n).comp F))
    (n : ℕ) (x : sections M t) (a₀ : N)
    (ha₀ : eval M t n (F a₀) = eval M t n x) :
    ∃ a : N, F a = x ∧ a - a₀ ∈ I ^ (n + 1) • (⊤ : Submodule R N) := by
  let G : (m : ℕ) → N →ₗ[R] M m := fun m => (eval M t m).comp F
  have hG : ∀ (m : ℕ) (a : N), t m (G (m + 1) a) = G m a :=
    fun m a => transition_eval M t m (F a)
  let C : ℕ → Type w := fun m => { a : N // G (n + m) a = x.val (n + m) }
  have hstart : G (n + 0) a₀ = x.val (n + 0) := ha₀
  have step : ∀ (m : ℕ) (a : C m),
      ∃ b : C (m + 1), b.val - a.val ∈
        I ^ (n + m + 1) • (⊤ : Submodule R N) := by
    intro m a
    have herr : x.val (n + m + 1) - G (n + m + 1) a.val ∈ (t (n + m)).ker := by
      change t (n + m) (x.val (n + m + 1) - G (n + m + 1) a.val) = 0
      rw [map_sub, x.property (n + m), hG, a.property, sub_self]
    rw [hker] at herr
    have hrange :
        (I ^ (n + m + 1) • (⊤ : Submodule R N)).map (G (n + m + 1)) =
          I ^ (n + m + 1) • (⊤ : Submodule R (M (n + m + 1))) := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr (hF (n + m + 1))]
    rw [← hrange] at herr
    obtain ⟨d, hd, hdeq⟩ := Submodule.mem_map.mp herr
    refine ⟨⟨a.val + d, ?_⟩, ?_⟩
    · change G (n + m + 1) (a.val + d) = x.val (n + m + 1)
      rw [map_add, hdeq, ← add_sub_assoc, add_sub_cancel_left]
    · change a.val + d - a.val ∈ I ^ (n + m + 1) • (⊤ : Submodule R N)
      simpa only [add_sub_cancel_left] using hd
  let c : (m : ℕ) → C m :=
    Nat.rec (motive := fun m : ℕ => C m) ⟨a₀, hstart⟩
      (fun m a => (step m a).choose)
  have hc : ∀ m : ℕ, (c (m + 1)).val - (c m).val ∈
      I ^ (n + m + 1) • (⊤ : Submodule R N) :=
    fun m => (step m (c m)).choose_spec
  have hcauchy : AdicCompletion.IsAdicCauchy I N (fun m => (c m).val) := by
    apply (AdicCompletion.isAdicCauchy_iff I N (fun m => (c m).val)).mpr
    intro m
    apply SModEq.symm
    apply SModEq.sub_mem.mpr
    apply Submodule.pow_smul_top_le I N
      ((Nat.le_add_left m n).trans (Nat.le_succ (n + m)))
    exact hc m
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I N) hcauchy
  have hFa : F a = x := by
    apply Subtype.ext
    apply funext
    intro k
    have hd : (c (k + 1)).val - a ∈ I ^ (k + 1) • (⊤ : Submodule R N) :=
      SModEq.sub_mem.mp (ha (k + 1))
    have hz : G k ((c (k + 1)).val - a) = 0 := by
      have hmem : G k ((c (k + 1)).val - a) ∈
          I ^ (k + 1) • (⊤ : Submodule R (M k)) :=
        Submodule.smul_top_le_comap_smul_top (I ^ (k + 1)) (G k) hd
      rw [hpow k] at hmem
      exact hmem
    have hck : G k (c (k + 1)).val = x.val k :=
      eval_eq_of_le M t ((Nat.le_succ k).trans (Nat.le_add_left (k + 1) n))
        (F (c (k + 1)).val) x (c (k + 1)).property
    rw [map_sub, hck] at hz
    exact (sub_eq_zero.mp hz).symm
  have hclose : ∀ m : ℕ, (c m).val - a₀ ∈
      I ^ (n + 1) • (⊤ : Submodule R N) := by
    intro m
    induction m with
    | zero =>
        change a₀ - a₀ ∈ I ^ (n + 1) • (⊤ : Submodule R N)
        rw [sub_self]
        exact Submodule.zero_mem _
    | succ m ih =>
        have hd : (c (m + 1)).val - (c m).val ∈
            I ^ (n + 1) • (⊤ : Submodule R N) :=
          Submodule.pow_smul_top_le I N
            (Nat.add_le_add_right (Nat.le_add_right n m) 1) (hc m)
        have hsum : ((c (m + 1)).val - (c m).val) + ((c m).val - a₀) ∈
            I ^ (n + 1) • (⊤ : Submodule R N) :=
          Submodule.add_mem _ hd ih
        simpa only [sub_add_sub_cancel] using hsum
  refine ⟨a, hFa, ?_⟩
  have hdiff : (c (n + 1)).val - a ∈ I ^ (n + 1) • (⊤ : Submodule R N) :=
    SModEq.sub_mem.mp (ha (n + 1))
  have hsub : ((c (n + 1)).val - a₀) - ((c (n + 1)).val - a) ∈
      I ^ (n + 1) • (⊤ : Submodule R N) :=
    Submodule.sub_mem _ (hclose (n + 1)) hdiff
  have heq : ((c (n + 1)).val - a₀) - ((c (n + 1)).val - a) = a - a₀ := by
    abel
  exact heq ▸ hsub

/-- Surjectivity at every finite level is effective for a complete source. -/
theorem surjective_of_surjective_components [IsPrecomplete I N]
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (F : N →ₗ[R] sections M t)
    (hF : ∀ n : ℕ, Function.Surjective ((eval M t n).comp F)) :
    Function.Surjective F := by
  intro x
  obtain ⟨a₀, ha₀⟩ := hF 0 (eval M t 0 x)
  obtain ⟨a, ha, _⟩ := exists_lift_with_congruence M t I hker hpow F hF 0 x a₀ ha₀
  exact ⟨a, ha⟩

end Approximation

section Finite

variable [∀ n : ℕ, Module.Finite R (M n)] [IsAdicComplete I R]

/-- Nakayama's lemma propagates a finite-level generating map from the
first level to all levels of an adic system. -/
theorem surjective_components_of_surjective_zero
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    {N : Type w} [AddCommGroup N] [Module R N]
    (F : N →ₗ[R] sections M t)
    (hF : Function.Surjective ((eval M t 0).comp F)) :
    ∀ n : ℕ, Function.Surjective ((eval M t n).comp F) := by
  intro n
  induction n with
  | zero => exact hF
  | succ n ih =>
      let G : N →ₗ[R] M (n + 1) := (eval M t (n + 1)).comp F
      have hgen : (⊤ : Submodule R (M (n + 1))) ≤
          G.range ⊔ I • (⊤ : Submodule R (M (n + 1))) := by
        intro y _
        obtain ⟨a, ha⟩ := ih (t n y)
        have hGa : t n (G a) = ((eval M t n).comp F) a :=
          transition_eval M t n (F a)
        have hd : y - G a ∈ (t n).ker := by
          change t n (y - G a) = 0
          rw [map_sub, hGa, ha, sub_self]
        rw [hker n] at hd
        have hdI : y - G a ∈ I • (⊤ : Submodule R (M (n + 1))) := by
          have hsmall : y - G a ∈ I ^ 1 • (⊤ : Submodule R (M (n + 1))) :=
            Submodule.pow_smul_top_le I (M (n + 1))
              (Nat.succ_le_succ (Nat.zero_le n)) hd
          simpa only [pow_one] using hsmall
        rw [← sub_add_cancel y (G a)]
        exact Submodule.add_mem _ (Submodule.mem_sup_right hdI)
          (Submodule.mem_sup_left (LinearMap.mem_range_self G a))
      have htop : (⊤ : Submodule R (M (n + 1))) ≤ G.range :=
        Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
          (IsAdicComplete.le_jacobson_bot (I := I)) hgen
      exact LinearMap.range_eq_top.mp (top_unique htop)

/-- A complete Noetherian base makes the actual compatible-sequence
module finite. No effective module is supplied as an input. -/
theorem finite [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥) :
    Module.Finite R (sections M t) := by
  obtain ⟨r, f₀, hf₀⟩ := Module.Finite.exists_fin' R (M 0)
  obtain ⟨F, hF⟩ := Module.projective_lifting_property (eval M t 0) f₀
    (eval_zero_surjective M t ht)
  have hF₀ : Function.Surjective ((eval M t 0).comp F) := by
    rw [hF]
    exact hf₀
  have hFn : ∀ n : ℕ, Function.Surjective ((eval M t n).comp F) :=
    surjective_components_of_surjective_zero M t I hker F hF₀
  have hcomplete : IsAdicComplete I (Fin r → R) :=
    IsAdicComplete.of_module_finite I (Fin r → R)
  exact Module.Finite.of_surjective F
    (surjective_of_surjective_components M t I hker hpow F hFn)

/-- Each finite stage is reached by the actual projection of the limit. -/
theorem eval_surjective
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (n : ℕ) : Function.Surjective (eval M t n) := by
  exact surjective_components_of_surjective_zero M t I hker
    (LinearMap.id : sections M t →ₗ[R] sections M t)
    (eval_zero_surjective M t ht) n

/-- The computed kernel of an actual projection is the corresponding
ideal power of the constructed finite module. -/
theorem ker_eval [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (n : ℕ) : (eval M t n).ker = I ^ (n + 1) • (⊤ : Submodule R (sections M t)) := by
  have hfinite : Module.Finite R (sections M t) := finite M t I ht hker hpow
  have hcomplete : IsAdicComplete I (sections M t) :=
    IsAdicComplete.of_module_finite I (sections M t)
  have hEval : ∀ k : ℕ,
      Function.Surjective ((eval M t k).comp
        (LinearMap.id : sections M t →ₗ[R] sections M t)) :=
    fun k => eval_surjective M t I ht hker k
  apply le_antisymm
  · intro x hx
    have hx₀ : eval M t n x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨a, ha, hcongr⟩ := exists_lift_with_congruence M t I hker hpow
      (LinearMap.id : sections M t →ₗ[R] sections M t) hEval n x 0
      (by
        change eval M t n 0 = eval M t n x
        rw [map_zero, hx₀])
    have ha' : a = x := ha
    simpa only [sub_zero, ha'] using hcongr
  · intro x hx
    have hmem : eval M t n x ∈ I ^ (n + 1) • (⊤ : Submodule R (M n)) :=
      Submodule.smul_top_le_comap_smul_top (I ^ (n + 1)) (eval M t n) hx
    rw [hpow n] at hmem
    exact LinearMap.mem_ker.mpr hmem

/-- The actual reduction of the constructed finite module recovers the
supplied finite stage. -/
def quotientEquiv [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (n : ℕ) :
    ((sections M t) ⧸ (I ^ (n + 1) • (⊤ : Submodule R (sections M t)))) ≃ₗ[R] M n :=
  (Submodule.quotEquivOfEq _ _ (ker_eval M t I ht hker hpow n).symm).trans
    ((eval M t n).quotKerEquivOfSurjective (eval_surjective M t I ht hker n))

/-- Recovery is induced by the original projection, with no change of
the maps of the supplied adic system. -/
theorem quotientEquiv_mk [IsNoetherianRing R]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (n : ℕ) (x : sections M t) :
    quotientEquiv M t I ht hker hpow n (Submodule.Quotient.mk x) = eval M t n x :=
  (eval M t n).quotKerEquivOfSurjective_apply_mk
    (eval_surjective M t I ht hker n) x

end Finite

end AdicModuleSystem
