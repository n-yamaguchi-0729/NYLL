/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.CompletionFromQuotientEquivalences
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Is Localization At Prime exists ring Equiv adic Completion maximal Ideal
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal

universe u v

namespace L1BAdic

theorem factorPow_evalₐ {S : Type u} [CommRing S] (J : Ideal S) {m n : ℕ} (hle : m ≤ n)
    (z : AdicCompletion J S) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n z) =
      AdicCompletion.evalₐ J m z :=
  AdicCompletion.factorPow_evalRing J hle z

theorem factorPow_evalₐ' {S : Type v} [CommRing S] (J : Ideal S) {m n : ℕ} (hle : m ≤ n)
    (z : AdicCompletion J S) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n z) =
      AdicCompletion.evalₐ J m z :=
  AdicCompletion.factorPow_evalRing J hle z

end L1BAdic

theorem _root_.IsLocalization.AtPrime.exists_ringEquiv_adicCompletion_maximalIdeal
    {B : Type u} [CommRing B] (𝔪 : Ideal B) [𝔪.IsMaximal]
    (O : Type v) [CommRing O] [IsLocalRing O] [Algebra B O] [IsLocalization.AtPrime O 𝔪] :
    ∃ ê : AdicCompletion 𝔪 B ≃+* AdicCompletion (IsLocalRing.maximalIdeal O) O,
      ∀ b : B, ê (algebraMap B (AdicCompletion 𝔪 B) b) =
        algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) (algebraMap B O b) :=
  AdicCompletion.exists_ringEquiv_of_quotientEquiv
    𝔪 (IsLocalRing.maximalIdeal O) (algebraMap B O)
    (fun n => (IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔪 O n).toRingEquiv)
    (fun n b => IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk 𝔪 O n b)

end IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
