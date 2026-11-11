/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The compatible quotient construction is extracted and generalized from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Reusing compatible quotient isomorphisms on adic completions

This is the existing localization-at-a-prime completion construction,
with the localization-specific finite-level equivalences made explicit
parameters. The original localization theorem can use this construction
directly; henselization supplies a second concrete application.
-/

@[expose] public section

noncomputable section

universe u v

namespace AdicCompletion

/-- Native ring-valued evaluation commutes with the quotient transition. -/
theorem factorPow_evalRing {R : Type u} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  change Ideal.Quotient.factorPow I hmn
      (AdicCompletion.evalₐ I n (AdicCompletion.mkₐ I a)) =
    AdicCompletion.evalₐ I m (AdicCompletion.mkₐ I a)
  rw [AdicCompletion.evalₐ_mkₐ, AdicCompletion.evalₐ_mkₐ,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk I hmn]

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S) (f : R →+* S)

/-- Isomorphisms of the actual power quotients preserving the original
ring map give an isomorphism of adic completions preserving that map. -/
theorem exists_ringEquiv_of_quotientEquiv
    (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
    (he : ∀ (n : ℕ) (a : R),
      e n (Ideal.Quotient.mk (I ^ n) a) = Ideal.Quotient.mk (J ^ n) (f a)) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ a : R, E (algebraMap R (AdicCompletion I R) a) =
        algebraMap S (AdicCompletion J S) (f a) := by
  have hefac : ∀ {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (e n x) =
        e m (Ideal.Quotient.factorPow I hmn x) := by
    intro m n hmn x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [he, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, he]
  have heinvfac : ∀ {m n : ℕ} (hmn : m ≤ n) (x : S ⧸ J ^ n),
      Ideal.Quotient.factorPow I hmn ((e n).symm x) =
        (e m).symm (Ideal.Quotient.factorPow J hmn x) := by
    intro m n hmn x
    obtain ⟨a, rfl⟩ := (e n).surjective x
    rw [RingEquiv.symm_apply_apply, hefac, RingEquiv.symm_apply_apply]
  let φ : AdicCompletion I R →+* AdicCompletion J S :=
    AdicCompletion.liftRingHom J
      (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) (by
        intro m n hmn
        apply RingHom.ext
        intro x
        change Ideal.Quotient.factorPow J hmn (e n (AdicCompletion.evalₐ I n x)) =
          e m (AdicCompletion.evalₐ I m x)
        rw [hefac, factorPow_evalRing])
  let ψ : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I
      (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) (by
        intro m n hmn
        apply RingHom.ext
        intro x
        change Ideal.Quotient.factorPow I hmn ((e n).symm (AdicCompletion.evalₐ J n x)) =
          (e m).symm (AdicCompletion.evalₐ J m x)
        rw [heinvfac, factorPow_evalRing])
  have hφ : ∀ (n : ℕ) (x : AdicCompletion I R),
      AdicCompletion.evalₐ J n (φ x) = e n (AdicCompletion.evalₐ I n x) :=
    fun n x => AdicCompletion.evalₐ_liftRingHom J _ _ n x
  have hψ : ∀ (n : ℕ) (x : AdicCompletion J S),
      AdicCompletion.evalₐ I n (ψ x) = (e n).symm (AdicCompletion.evalₐ J n x) :=
    fun n x => AdicCompletion.evalₐ_liftRingHom I _ _ n x
  refine ⟨RingEquiv.ofRingHom φ ψ ?_ ?_, fun a => ?_⟩
  · apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hφ, hψ, RingEquiv.apply_symm_apply, RingHom.id_apply]
  · apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hψ, hφ, RingEquiv.symm_apply_apply, RingHom.id_apply]
  · change φ (AdicCompletion.of I R a) = AdicCompletion.of J S (f a)
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hφ, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, he]

end AdicCompletion
