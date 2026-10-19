/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Cohomology.SerrePairing
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.WeilSmulEqRiemannIndexFormula

/-!
# Eq zero or exists eq weil Of Kaehler smul of mem omega Space
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.EqZeroOrExistsWeilOfKaehlerSmul
open AlgebraicCurve

namespace ModularCurve
namespace OmegaSide
namespace A

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kaehlerResidueTerm_smulF_left [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F]
    (f : F) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (f • ω) α v = kaehlerResidueTerm ω (mulAdele K f α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply]
  ring_nf

theorem weilOfKaehler_smulF [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F] [HasCanonicalDivisor (K := K)
      (F := F)]
    {f : F} {ω : Ω[F⁄K]} (hω : ω ≠ 0) (hf : f ≠ 0) :
    weilOfKaehler K F (ω := f • ω) (smul_ne_zero hf hω) = weilSmul K F f (weilOfKaehler K F hω)
      := by
  apply LinearMap.ext
  intro α
  rw [weilSmul_apply, weilOfKaehler_apply, weilOfKaehler_apply]
  refine finsum_congr fun v => ?_
  rw [kaehlerResidueTerm_smulF_left, adeleSpaceMul_coe]

theorem eq_zero_or_exists_eq_weilOfKaehler_smul'
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasCanonicalLocalResidueKStar K F]
    (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (D : Divisor K F)
    (μ : Module.Dual K (adeleSpace K F)) (hμ : μ ∈ omegaSpace (K := K) (F := F) D) :
    μ = 0 ∨ ∃ (f : F) (hf : f ≠ 0), μ = weilOfKaehler K F (ω := f • ω₀) (smul_ne_zero hf hω₀) := by
  classical
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨hl0, hlmem, hlmax⟩ := hagree hω₀
  set W₀ := canonicalDivisorOf hω₀
  have h1 : omegaSpace (K := K) (F := F) W₀ ≤ omegaSpace (W₀ ⊓ D) := omegaSpace_antitone inf_le_left
  have h2 : omegaSpace (K := K) (F := F) D ≤ omegaSpace (W₀ ⊓ D) := omegaSpace_antitone inf_le_right
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_riemannIndexFormula hRI (h1 hlmem) (h2 hμ) hl0
  by_cases hf0 : f = 0
  · left
    rw [hf, hf0]
    apply LinearMap.ext; intro α
    rw [weilSmul_apply, LinearMap.zero_apply]
    have : adeleSpaceMul K F (0 : F) α = 0 := by
      apply Subtype.ext
      rw [adeleSpaceMul_coe]
      exact funext fun v => zero_mul (α.val v)
    rw [this, map_zero]
  · right
    exact ⟨f, hf0, by rw [weilOfKaehler_smulF hω₀ hf0, hf]⟩

end ModularCurve.OmegaSide.A

open ModularCurve.OmegaSide.A in
theorem _root_.AlgebraicCurve.eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasCanonicalLocalResidueKStar K F]
    (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (D : Divisor K F)
    (μ : Module.Dual K (adeleSpace K F)) (hμ : μ ∈ omegaSpace (K := K) (F := F) D) :
    μ = 0 ∨ ∃ (f : F) (hf : f ≠ 0), μ = weilOfKaehler K F (ω := f • ω₀) (smul_ne_zero hf hω₀) :=
  eq_zero_or_exists_eq_weilOfKaehler_smul' hRI hagree hω₀ D μ hμ
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.EqZeroOrExistsWeilOfKaehlerSmul
end ProofImplementation
