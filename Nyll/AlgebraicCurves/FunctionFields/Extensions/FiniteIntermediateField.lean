/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_intermediateField_of_transcendental_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteSimpleExtensions
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Finite intermediate Field of transcendental mem
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Finite_intermediateField_of_transcendental_mem

namespace S2Finite

open IntermediateField

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem finiteDimensional_adjoin_of_transcendental {x₀ : F} (_ : Transcendental K x₀)
    (hfd : FiniteDimensional K⟮x₀⟯ F) {t : F} (ht : Transcendental K t) : FiniteDimensional K⟮t⟯ F
      := by
  let : FiniteDimensional K⟮x₀⟯ F := hfd
  exact _root_.AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x₀ ht

end S2Finite

open IntermediateField in
theorem _root_.AlgebraicCurve.finite_intermediateField_of_transcendental_mem
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : L) (htE : t ∈ E) (ht : Transcendental K t)
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set
      L)) L) :
    Module.Finite ↥E L := by
  obtain ⟨x, hx, hfd⟩ := hfg
  have hfin : FiniteDimensional K⟮t⟯ L := S2Finite.finiteDimensional_adjoin_of_transcendental hx
    hfd ht
  have hle : K⟮t⟯ ≤ E := IntermediateField.adjoin_simple_le_iff.mpr htE
  let : Algebra K⟮t⟯ E := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K⟮t⟯ E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K⟮t⟯ E L
end AlgebraicCurves.FunctionFields.Proofs.Finite_intermediateField_of_transcendental_mem
end ProofImplementation
