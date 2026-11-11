/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Henselian.AlgHomLiftIsSmoothAt
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Residue-preserving approximation of an actual smooth completion stage

A given map from a smooth algebra to the maximal-adic completion supplies
an actual residue-field point. Henselian lifting returns an algebra map to
the original ring preserving that point. Composition retains the closed
point of any given factorization through this smooth stage.

Existence of a smooth factorization of an arbitrary completion map is a
separate input; this file does not assert that existence.
-/

@[expose] public section

noncomputable section

universe u

namespace HenselianLocalRing

open IsLocalRing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- A smooth completion stage has an approximation in the original
henselian local ring with the same actual closed point. -/
theorem exists_smooth_completion_approximation
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (β : S →ₐ[R] AdicCompletion (maximalIdeal R) R) :
    ∃ ψ : S →ₐ[R] R, ∀ s,
      algebraMap R (ResidueField R) (ψ s) = AdicCompletion.evalOneₐ (maximalIdeal R) (β s) := by
  let φ : S →ₐ[R] ResidueField R := (AdicCompletion.evalOneₐ (maximalIdeal R)).comp β
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  exact exists_algHom_lift_of_isSmoothAt S φ

/-- An actual smooth factorization gives an approximation of the original
map, with its original reduction to the closed point unchanged. -/
theorem exists_completion_approximation_of_smooth_factorization
    (B S : Type u) [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    [Algebra.Smooth R S] (f : B →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (α : B →ₐ[R] S) (β : S →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (h : β.comp α = f) :
    ∃ ψ : B →ₐ[R] R, ∀ b,
      algebraMap R (ResidueField R) (ψ b) = AdicCompletion.evalOneₐ (maximalIdeal R) (f b) := by
  obtain ⟨ψ, hψ⟩ := exists_smooth_completion_approximation S β
  refine ⟨ψ.comp α, fun b => ?_⟩
  change algebraMap R (ResidueField R) (ψ (α b)) = _
  rw [hψ]
  exact congrArg (AdicCompletion.evalOneₐ (maximalIdeal R)) (DFunLike.congr_fun h b)

end HenselianLocalRing
