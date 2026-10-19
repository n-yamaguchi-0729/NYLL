/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusMultiplicativeJets
import Nyll.AlgebraicCurves.Differentials.Logarithmic.Logarithmic
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry
import Nyll.AlgebraicCurves.Differentials.Residues.Basic

/-!
# Differential estimates for principal units

For a smooth function field over a perfect field, differentiation lowers a
positive maximal-ideal power by at most one. Consequently the residue of
`f dlog(g)` vanishes when `g` is one modulo a power strictly greater than the
pole order of `f`. The local congruence is the actual ideal-power condition.
-/

noncomputable section

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A positive principal-unit congruence gives an integral uniformizer-power
expansion, including the case where the principal unit is exactly one. -/
theorem CongruentOne.exists_uniformizer_expansion {v : Place K F} {n : ℕ} {g : F}
    (hg : v.CongruentOne (n + 1) g) :
    ∃ h : F, h ∈ v.toValuationSubring ∧ g = 1 + v.uniformizer ^ (n + 1) * h := by
  have hb := (v.congruentOne_iff_adicValuation_sub_one_le (Nat.succ_ne_zero n) g).mp hg
  rcases v.adicValuation_le_exp_iff.mp hb with hzero | hord
  · refine ⟨0, zero_mem _, ?_⟩
    rw [mul_zero, add_zero]
    exact sub_eq_zero.mp hzero
  · by_cases hzero : g - 1 = 0
    · refine ⟨0, zero_mem _, ?_⟩
      rw [mul_zero, add_zero]
      exact sub_eq_zero.mp hzero
    · refine ⟨(g - 1) / v.uniformizer ^ (n + 1), ?_, ?_⟩
      · apply v.mem_toValuationSubring_of_ord_nonneg
        rw [div_eq_mul_inv, v.ord_mul hzero
          (inv_ne_zero (pow_ne_zero (n + 1) v.uniformizer_ne_zero)), v.ord_inv,
          ← zpow_natCast, v.ord_zpow, v.ord_uniformizer, mul_one]
        omega
      · rw [mul_div_cancel₀ _ (pow_ne_zero (n + 1) v.uniformizer_ne_zero)]
        ring

variable [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- Differentiating an integral function gives an integral differential
coefficient. This is supplied by smooth function-field geometry. -/
theorem differentialCoeff_D_mem_of_integral (v : Place K F) {h : F}
    (hh : h ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring := by
  let : v.DCoordGenerates := dCoordGenerates_of_isCurveOver v
  let : Nontrivial Ω[F⁄K] := Module.nontrivial_of_finrank_eq_succ
    (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2
  obtain ⟨c, hc, he⟩ := exists_mem_D_eq_smul_D_of_isCurveOver v v.ord_uniformizer hh
  have heq : v.differentialCoeff (KaehlerDifferential.D K F h) = c :=
    v.differentialCoeff_unique he
  exact heq.symm ▸ hc

/-- The derivative of a unit congruent to one modulo the `(n+1)`st power has
its coefficient in the `n`th power. -/
theorem CongruentOne.exists_differentialCoeff_eq_pow_mul {v : Place K F}
    {n : ℕ} {g : F} (hg : v.CongruentOne (n + 1) g) :
    ∃ c : F, c ∈ v.toValuationSubring ∧
      v.differentialCoeff (KaehlerDifferential.D K F g) = v.uniformizer ^ n * c := by
  let : v.DCoordGenerates := dCoordGenerates_of_isCurveOver v
  let : Nontrivial Ω[F⁄K] := Module.nontrivial_of_finrank_eq_succ
    (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2
  obtain ⟨h, hh, he⟩ := hg.exists_uniformizer_expansion
  let c := v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F h)
    + h * (n + 1 : ℕ)
  have hπ : v.uniformizer ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg (by rw [v.ord_uniformizer]; norm_num)
  refine ⟨c, add_mem (mul_mem hπ (v.differentialCoeff_D_mem_of_integral hh))
    (mul_mem hh (natCast_mem _ _)), ?_⟩
  apply v.differentialCoeff_unique
  rw [he, map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Derivation.leibniz_pow, Nat.add_sub_cancel, ← v.dCoord_eq,
    ← v.differentialCoeff_smul_dCoord (KaehlerDifferential.D K F h),
    ← Nat.cast_smul_eq_nsmul F (n + 1), smul_smul, smul_smul, smul_smul,
    ← add_smul]
  congr 1
  dsimp only [c]
  rw [pow_succ]
  ring

/-- A function of pole order at most `n` times the logarithmic derivative of
a principal unit of level `n+1` has integral differential coefficient. -/
theorem CongruentOne.mul_dlog_coefficient_mem {v : Place K F} {n : ℕ} {f g : F}
    (hg : v.CongruentOne (n + 1) g) (hf : -(n : ℤ) ≤ v.ord f) :
    f * v.differentialCoeff (dlog K g) ∈ v.toValuationSubring := by
  let : v.DCoordGenerates := dCoordGenerates_of_isCurveOver v
  let : Nontrivial Ω[F⁄K] := Module.nontrivial_of_finrank_eq_succ
    (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2
  obtain ⟨c, hc, he⟩ := hg.exists_differentialCoeff_eq_pow_mul
  have hginv : g⁻¹ ∈ v.toValuationSubring := by
    obtain ⟨u, hu, _⟩ := hg.inv
    exact hu ▸ u.val.2
  have hfpow : f * v.uniformizer ^ n ∈ v.toValuationSubring := by
    by_cases hfzero : f = 0
    · rw [hfzero, zero_mul]
      exact zero_mem _
    · apply v.mem_toValuationSubring_of_ord_nonneg
      rw [v.ord_mul hfzero (pow_ne_zero n v.uniformizer_ne_zero),
        ← zpow_natCast, v.ord_zpow, v.ord_uniformizer, mul_one]
      omega
  rw [dlog, v.differentialCoeff_smul, he,
    show f * (g⁻¹ * (v.uniformizer ^ n * c)) =
      (f * v.uniformizer ^ n) * (g⁻¹ * c) by ring]
  exact mul_mem hfpow (mul_mem hginv hc)

/-- The local additive symbol vanishes at the explicit pole-order-plus-one
bound. No local-symbol existence or modulus hypothesis is used. -/
theorem CongruentOne.localResidue_mul_dlog_eq_zero
    [HasCanonicalLocalResidueKStar K F] {v : Place K F} {n : ℕ} {f g : F}
    (hg : v.CongruentOne (n + 1) g) (hf : -(n : ℤ) ≤ v.ord f) :
    v.localResidue (f * v.differentialCoeff (dlog K g)) = 0 :=
  v.localResidue_of_mem (hg.mul_dlog_coefficient_mem hf)

end AlgebraicCurve.Place
