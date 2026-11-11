/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialSpanDEqTop
public import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialDNeZero
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Kaehler Differential exists unique smul D of transcendental
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Differentials.Kaehler.Proofs
namespace KaehlerDifferential_exists_unique_smul_D_of_transcendental

namespace KaehlerDifferential
open _root_.KaehlerDifferential
end KaehlerDifferential
open scoped _root_.KaehlerDifferential in
private theorem KaehlerDifferential.exists_unique_smul_D_of_transcendental (K : Type*) [Field K] {F
  : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [Algebra.IsSeparable
  (IntermediateField.adjoin K ({x} : Set F)) F] (ω : KaehlerDifferential K F) : ∃! c : F, ω = c •
  KaehlerDifferential.D K F x := by
  have hmem : ω ∈ Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F))
    := by
    rw [KaehlerDifferential.span_D_eq_top_of_transcendental K x hx]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, rfl, fun c' hc' => ?_⟩
  have h : (c' - c) • KaehlerDifferential.D K F x = 0 := by rw [sub_smul, ← hc', sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (KaehlerDifferential.D_ne_zero_of_transcendental K x hx)

open KaehlerDifferential_exists_unique_smul_D_of_transcendental.KaehlerDifferential
  renaming exists_unique_smul_D_of_transcendental → uniqueSmulProof in
theorem _root_.KaehlerDifferential.exists_unique_smul_D_of_transcendental (K : Type*) [Field K] {F
  : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [Algebra.IsSeparable
  (IntermediateField.adjoin K ({x} : Set F)) F] (ω : KaehlerDifferential K F) : ∃! c : F, ω = c •
  KaehlerDifferential.D K F x :=
  uniqueSmulProof K x hx ω

end KaehlerDifferential_exists_unique_smul_D_of_transcendental
end AlgebraicCurves.Differentials.Kaehler.Proofs
end ProofImplementation
