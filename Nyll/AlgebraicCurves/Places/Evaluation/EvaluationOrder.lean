/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).

Source-file correspondence is unconfirmed for:
Place_evalAt_eq_zero_iff_one_le_ord
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place mem and eval At eq iff ord sub algebra Map pos
-/

section

namespace AlgebraicCurve.Place

theorem mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) (f : F) (a : K) (hfa : f ≠ algebraMap K F a) :
    (f ∈ v.toValuationSubring ∧ v.evalAt f = a) ↔ 0 < v.ord (f - algebraMap K F a) := by
  classical
  have hfa' : f - algebraMap K F a ≠ 0 := sub_ne_zero.mpr hfa
  have hamem : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  constructor
  · rintro ⟨hf, hev⟩
    have hmem : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hf hamem
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f - algebraMap K F a, hmem⟩ = 0 := by
      have h1 : (⟨f - algebraMap K F a, hmem⟩ : v.toValuationSubring) = ⟨f, hf⟩ - ⟨algebraMap K F
        a, hamem⟩ := rfl
      rw [h1, map_sub, ← v.algebraMap_evalAt hv hf, hev]
      have h2 : (⟨algebraMap K F a, hamem⟩ : v.toValuationSubring) = algebraMap K
        v.toValuationSubring a := rfl
      rw [h2, sub_eq_zero]
      exact (IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField a).symm
    exact (v.mem_maximalIdeal_iff_ord_pos hfa' hmem).mp
      ((IsLocalRing.residue_eq_zero_iff _).mp hres)
  · intro hpos
    have hmem : f - algebraMap K F a ∈ v.toValuationSubring := v.mem_of_ord_nonneg hfa' hpos.le
    have hf : f ∈ v.toValuationSubring := by
      have : f = (f - algebraMap K F a) + algebraMap K F a := by ring
      rw [this]; exact add_mem hmem hamem
    refine ⟨hf, ?_⟩
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f - algebraMap K F a, hmem⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((v.mem_maximalIdeal_iff_ord_pos hfa' hmem).mpr hpos)
    have h1 : (⟨f - algebraMap K F a, hmem⟩ : v.toValuationSubring) = ⟨f, hf⟩ - ⟨algebraMap K F a,
      hamem⟩ := rfl
    rw [h1, map_sub, sub_eq_zero] at hres
    rw [v.evalAt_of_mem hf, hres]
    have h2 : (⟨algebraMap K F a, hamem⟩ : v.toValuationSubring) = algebraMap K
      v.toValuationSubring a := rfl
    rw [h2]
    have h3 : IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring a) =
      algebraMap K v.ResidueField a :=
      (IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField a).symm
    rw [h3, v.residueInv_algebraMap]

end AlgebraicCurve.Place

end

section

/-!
# Place eval At eq zero iff one le ord
-/

namespace AlgebraicCurve.Place

theorem evalAt_eq_zero_iff_one_le_ord {K F : Type*} [Field K] [Field F]
    [Algebra K F] (x : Place K F) (hx : x.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ x.toValuationSubring) : x.evalAt f = 0 ↔ 1 ≤ x.ord f := by
  have hfa : f ≠ algebraMap K F (0 : K) := by
    rw [map_zero]
    exact hf0
  have h := x.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos hx f 0 hfa
  rw [map_zero, sub_zero] at h
  constructor
  · intro hEval
    have hpos := h.mp ⟨hf, hEval⟩
    omega
  · intro hOrd
    exact (h.mpr (by omega)).2

end AlgebraicCurve.Place

end
