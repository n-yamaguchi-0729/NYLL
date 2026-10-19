/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LocalSections.RROpensInjectiveMemEllSubSumSingleAddEqEll
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Simultaneous point selection in the nonspecial range, using the common exact-drop theorem. -/

universe u v w

namespace AlgebraicCurve.RROpens

theorem exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    {N : ℕ} (D : Fin N → Divisor K F) (hdeg : ∀ k, Divisor.degree (D k) = r)
    {ι : Type w} [Fintype ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * r * b ^ (r - g) + (r - g) < Fintype.card ι) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin (r - g) → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) = 1 := by
  classical
  have hKc : Divisor.degree Kc = 2 * (g : ℤ) - 2 := by
    have h0 := hRR 0
    have h1 := hRR Kc
    rw [sub_zero, map_zero] at h0
    rw [sub_self] at h1
    linarith
  have hellD : ∀ k, ell (D k) = r - g + 1 := by
    intro k
    have hz : ell (Kc - D k) = 0 :=
      ell_eq_zero_of_degree_neg (by rw [map_sub, hKc, hdeg k]; omega)
    have h := hRR (D k)
    rw [hz, hdeg k] at h
    omega
  obtain ⟨a, ha, hell⟩ :=
    exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
      D (r - g) r (fun k => by rw [hellD k]; omega)
      (fun k => (hdeg k).le) B hB hdisj hb1 hb hcard
  refine ⟨a, ha, fun k v hv => ?_⟩
  have h := hell k v hv
  rw [hellD k] at h
  omega

end AlgebraicCurve.RROpens
