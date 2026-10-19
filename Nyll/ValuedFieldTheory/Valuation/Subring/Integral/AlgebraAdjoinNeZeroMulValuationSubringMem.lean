/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Algebra exists adjoin ne zero mul forall valuation Subring mem
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem

open Polynomial

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem _root_.Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q₀ : Algebra.adjoin L ({f} : Set F), q₀ ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → (q₀ : F) * z ∈ V := by
  classical
  let Lf : Subalgebra L F := Algebra.adjoin L ({f} : Set F)
  let Kf : IntermediateField L F := IntermediateField.adjoin L ({f} : Set F)
  have hz : IsIntegral Kf z := IsIntegral.of_finite Kf z
  obtain ⟨⟨m, hm⟩, hint⟩ :=
    hz.exists_multiple_integral_of_isLocalization (nonZeroDivisors Lf)
  refine ⟨m, mem_nonZeroDivisors_iff_ne_zero.mp hm, fun V hL hfV => ?_⟩
  have hsmul : (m : F) * z = (m : Lf) • z := (Algebra.smul_def m z).symm
  rw [hsmul]
  set s : Set F := Set.range (algebraMap L F) ∪ {f}
  have hcl : Subring.closure s = Lf.toSubring :=
    (Algebra.adjoin_eq_ring_closure ({f} : Set F)).symm
  have hint2 : IsIntegral (Subring.closure s) ((m : Lf) • z) := by
    refine hint.map_of_comp_eq (Subring.inclusion hcl.ge) (RingHom.id F) ?_
    ext a; rfl
  have hmem : (m : Lf) • z ∈ (integralClosure (Subring.closure s) F).toSubring := hint2
  rw [← iInf_valuationSubring_superset (s := s)] at hmem
  simp only [Subring.mem_iInf] at hmem
  exact hmem ⟨V, fun x hx => hx.elim (fun ⟨c, hc⟩ => hc ▸ hL c) (fun hx => hx ▸ hfV)⟩
end
end AlgebraicCurves.Valuations.Proofs.Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
end ProofImplementation
