/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusFFSubOneEqSplittingFieldDvdOrdNatCastNeZero

/-!
# Kummer genus formula in characteristic zero
-/

namespace AlgebraicCurve

open Polynomial

theorem genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {q : ℕ} [Fact q.Prime] {f : F} (hf : ∀ g : F, g ^ q ≠ f)
    (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C f)] :
    (genusFF L F' : ℤ) - 1 = q * ((genusFF L F : ℤ) - 1) := by
  have hq : q.Prime := Fact.out
  exact genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero
    hF (Nat.cast_ne_zero.mpr hq.ne_zero) hf hdvd F'

end AlgebraicCurve
