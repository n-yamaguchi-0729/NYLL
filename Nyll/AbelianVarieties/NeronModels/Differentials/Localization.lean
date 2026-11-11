/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Localization.Module
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms

/-!
# Generators of top forms after localization
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra.TopFormOrder

universe u

theorem span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
    (R K B B' : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R])) :
    let _ : Module B (⋀[B']^d (Ω[B'⁄K])) := moduleAlong B B' (⋀[B']^d (Ω[B'⁄K]))
    Submodule.span B' {topFormMap R K B B' d (exteriorPower.ιMulti B d β)} = ⊤ ∧
      ∀ σ : ⋀[B']^d (Ω[B'⁄K]), Submodule.span B' {σ} = ⊤ →
        ∃ u : B'ˣ, σ = (u : B') • topFormMap R K B B' d (exteriorPower.ιMulti B d β) := by
  classical
  intro moduleB
  have hM : Algebra.algebraMapSubmonoid B (Submonoid.powers ϖ) =
      Submonoid.powers (algebraMap R B ϖ) :=
    Submonoid.map_powers _ _
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers ϖ)) B' := by
    rw [hM]; infer_instance
  have : IsLocalizedModule (Submonoid.powers ϖ)
      ((KaehlerDifferential.map R K B B').restrictScalars R) :=
    KaehlerDifferential.isLocalizedModule R K B B' (Submonoid.powers ϖ)
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid B (Submonoid.powers ϖ))
      (KaehlerDifferential.map R K B B') :=
    IsLocalizedModule.of_restrictScalars (Submonoid.powers ϖ) _
  let bK : Module.Basis (Fin d) B' (Ω[B'⁄K]) :=
    β.ofIsLocalizedModule B' (Algebra.algebraMapSubmonoid B (Submonoid.powers ϖ))
      (KaehlerDifferential.map R K B B')
  set v : Fin d → Ω[B'⁄K] := fun i => KaehlerDifferential.map R K B B' (β i) with hv
  have hbK : (bK : Fin d → Ω[B'⁄K]) = v := by
    funext i; simp only [bK, Module.Basis.ofIsLocalizedModule_apply, hv]
  have hρ : topFormMap R K B B' d (exteriorPower.ιMulti B d β) = exteriorPower.ιMulti B' d v := by
    exact AbelianVarieties.NOSProofs.TopFormComposition.BenchOTFMComp.topFormMap_ιMulti
      R K B B' d β
  obtain ⟨hspan, hfree⟩ :=
    AbelianVarieties.NOSProofs.TopFormNonvanishing.P2mFrameNZ.exists_smul_ιMulti_and_smul_injective
      d bK
  rw [hbK] at hspan hfree
  rw [hρ]
  refine ⟨?_, fun σ hσ => ?_⟩
  · refine Submodule.eq_top_iff'.mpr fun η => ?_
    obtain ⟨c, hc⟩ := hspan η
    exact hc ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · obtain ⟨c, hc⟩ := hspan σ
    have hmem : exteriorPower.ιMulti B' d v ∈ Submodule.span B' {σ} := by rw [hσ]; trivial
    obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hmem
    have hgc : g * c = 1 := hfree _ _ (by rw [mul_smul, ← hc, hg, one_smul])
    exact ⟨⟨c, g, by rw [mul_comm]; exact hgc, hgc⟩, hc⟩

end NeronModelInfra.TopFormOrder
end
