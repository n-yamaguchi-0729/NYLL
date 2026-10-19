/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.StrictExactness
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.Filtration

/-!
# Completion of direct sums of one finite exact sequence

One Artin–Rees bound for an inclusion of finite modules controls every
coordinate of its direct sum, even when the index set is infinite.
The explicit bound therefore supplies exactness after completion for
these direct sums. This is the uniform estimate used to prove flatness
of the completion of an arbitrary free module.
-/

noncomputable section

universe u v w t a

namespace Finsupp

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {α : Type a}

/-- Membership in an ideal times a direct sum is coordinatewise
membership in the ideal times the coefficient module. -/
theorem mem_ideal_smul_top_iff (J : Ideal R) (x : α →₀ M) :
    x ∈ (J • ⊤ : Submodule R (α →₀ M)) ↔
      ∀ i : α, x i ∈ (J • ⊤ : Submodule R M) := by
  classical
  constructor
  · intro hx i
    have hle : Submodule.map (Finsupp.lapply i) (J • ⊤ : Submodule R (α →₀ M)) ≤
        (J • ⊤ : Submodule R M) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right J le_top
    exact hle ⟨x, hx, rfl⟩
  · intro hx
    rw [← Finsupp.sum_single x]
    apply Submodule.sum_mem
    intro i _
    have hle : Submodule.map (Finsupp.lsingle i) (J • ⊤ : Submodule R M) ≤
        (J • ⊤ : Submodule R (α →₀ M)) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right J le_top
    exact hle ⟨x i, hx i, rfl⟩

end Finsupp

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type t} [AddCommGroup P] [Module R P]

/-- The composite of coefficient maps induces the composite of the
corresponding maps on completed direct sums. -/
theorem map_finsupp_comp_apply (α : Type a) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (x : AdicCompletion I (α →₀ M)) :
    map I (Finsupp.mapRange.linearMap (α := α) (g.comp f)) x =
      map I (Finsupp.mapRange.linearMap (α := α) g)
        (map I (Finsupp.mapRange.linearMap (α := α) f) x) := by
  rw [Finsupp.mapRange.linearMap_comp]
  exact (AdicCompletion.map_comp_apply I (Finsupp.mapRange.linearMap f)
    (Finsupp.mapRange.linearMap g) x).symm

/-- Artin–Rees supplies an explicit bound for the adic filtration
induced by an injection into a finite module. -/
theorem exists_adic_bound_of_injective [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • ⊤ : Submodule R N) ≤
        (I ^ n • ⊤ : Submodule R M) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, ?_⟩
  intro n x hx
  have hnum : n + k - k = n := by omega
  have hidentity :
      (I ^ (n + k) • ⊤ : Submodule R N) ⊓ LinearMap.range f =
        I ^ n • ((I ^ k • ⊤ : Submodule R N) ⊓ LinearMap.range f) := by
    rw [hk (n + k) (by omega), hnum]
  have hsmall : f x ∈
      I ^ n • ((I ^ k • ⊤ : Submodule R N) ⊓ LinearMap.range f) := by
    rw [← hidentity]
    exact ⟨hx, ⟨x, rfl⟩⟩
  have himage : f x ∈ Submodule.map f (I ^ n • ⊤ : Submodule R M) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    have hle : I ^ n • ((I ^ k • ⊤ : Submodule R N) ⊓ LinearMap.range f) ≤
        I ^ n • LinearMap.range f := smul_mono_right (I ^ n) inf_le_right
    exact hle hsmall
  have hmem : x ∈ Submodule.comap f (Submodule.map f
      (I ^ n • ⊤ : Submodule R M)) := himage
  rw [Submodule.comap_map_eq_of_injective hf] at hmem
  exact hmem

/-- A single bound for a map also bounds its map on an arbitrary
direct sum of copies. -/
theorem finsupp_adic_bound (α : Type a) (f : M →ₗ[R] N) (k : ℕ)
    (hbound : ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • ⊤ : Submodule R N) ≤
        (I ^ n • ⊤ : Submodule R M)) (n : ℕ) :
    Submodule.comap (Finsupp.mapRange.linearMap (α := α) f)
        (I ^ (n + k) • ⊤ : Submodule R (α →₀ N)) ≤
      (I ^ n • ⊤ : Submodule R (α →₀ M)) := by
  intro x hx
  apply (Finsupp.mem_ideal_smul_top_iff (I ^ n) x).mpr
  intro i
  apply hbound n
  exact (Finsupp.mem_ideal_smul_top_iff (I ^ (n + k))
    (Finsupp.mapRange.linearMap f x)).mp hx i

/-- Completion preserves the direct sum, over any index set, of a
short exact sequence whose middle module is finite over a Noetherian
ring. The direct sums themselves need not be finite. -/
theorem map_finsupp_exact [IsNoetherianRing R] [Module.Finite R N]
    (α : Type a) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact
      (map I (Finsupp.mapRange.linearMap (α := α) f))
      (map I (Finsupp.mapRange.linearMap (α := α) g)) := by
  obtain ⟨k, hk⟩ := exists_adic_bound_of_injective I f hf
  apply map_exact_of_adic_bound I _ _ _ _ k (finsupp_adic_bound I α f k hk)
  · rw [LinearMap.exact_iff, Finsupp.ker_mapRange,
      Finsupp.range_mapRange_linearMap f (LinearMap.ker_eq_bot.mpr hf),
      hfg.linearMap_ker_eq]
  · exact Finsupp.mapRange_surjective g g.map_zero hg

/-- The right-hand map need not be surjective when its target is also
finite. Factor it through its actual image and apply Artin–Rees to the
image inclusion. -/
theorem map_finsupp_exact_of_finite [IsNoetherianRing R]
    [Module.Finite R N] [Module.Finite R P]
    (α : Type a) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact
      (map I (Finsupp.mapRange.linearMap (α := α) f))
      (map I (Finsupp.mapRange.linearMap (α := α) g)) := by
  have hrestricted : Function.Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, hfg.linearMap_ker_eq]
  have hexact := map_finsupp_exact I α f g.rangeRestrict hf hrestricted
    g.surjective_rangeRestrict
  obtain ⟨k, hk⟩ := exists_adic_bound_of_injective I (LinearMap.range g).subtype
    (Submodule.injective_subtype _)
  have hinj := map_injective_of_adic_bound I
    (Finsupp.mapRange.linearMap (α := α) (LinearMap.range g).subtype) k
      (finsupp_adic_bound I α _ k hk)
  have h := hinj.comp_exact_iff_exact.mpr hexact
  rw [map_comp, ← Finsupp.mapRange.linearMap_comp,
    LinearMap.subtype_comp_rangeRestrict] at h
  exact h

end AdicCompletion
