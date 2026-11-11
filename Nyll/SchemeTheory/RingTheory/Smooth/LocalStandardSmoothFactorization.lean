/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Standard smooth stages for a map into a local ring

A map from a smooth algebra into a local ring factors through a
standard smooth principal localization. The principal open is chosen
at the inverse image of the target's closed point, so its defining
element maps to a unit and the actual map extends to the localization.
-/

@[expose] public section

noncomputable section

namespace Algebra

/-- Every map from a smooth algebra into a local ring extends to an
actual standard smooth principal localization of its source. -/
theorem Smooth.exists_standardSmooth_localization_factorization
    {R B L : Type*} [CommRing R] [CommRing B] [CommRing L]
    [Algebra R B] [Algebra R L] [Smooth R B] [IsLocalRing L]
    (φ : B →ₐ[R] L) :
    ∃ f : B, IsStandardSmooth R (Localization.Away f) ∧
      ∃ ψ : Localization.Away f →ₐ[R] L,
        ψ.comp (IsScalarTower.toAlgHom R B (Localization.Away f)) = φ := by
  let p : Ideal B := (IsLocalRing.maximalIdeal L).comap φ.toRingHom
  have : p.IsPrime := Ideal.comap_isPrime φ.toRingHom (IsLocalRing.maximalIdeal L)
  obtain ⟨f, hf, hstd⟩ := IsSmoothAt.exists_notMem_isStandardSmooth R p
  have hu : IsUnit (φ f) := IsLocalRing.notMem_maximalIdeal.mp hf
  let ψ : Localization.Away f →ₐ[R] L :=
    IsLocalization.Away.liftAlgHom f hu
  refine ⟨f, hstd, ψ, ?_⟩
  apply AlgHom.ext
  intro b
  exact IsLocalization.Away.lift_eq f hu b

end Algebra
