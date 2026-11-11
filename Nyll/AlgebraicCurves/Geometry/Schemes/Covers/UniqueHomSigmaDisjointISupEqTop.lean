/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Scheme exists Unique hom sigma of disjoint i Sup eq top
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem _root_.AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top
    {σ : Type v} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (U : σ → T.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤)
    (v : ∀ i, ((U i : T.Opens) : Scheme.{u}) ⟶ H i) :
    ∃! u : T ⟶ ∐ H, ∀ i, (U i).ι ≫ u = v i ≫ Sigma.ι H i := by
  have hcover : (⨆ i, (U i).ι.opensRange) = ⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using hcov
  have hpair : Pairwise (fun i j => Disjoint (U i).ι.opensRange (U j).ι.opensRange) := by
    intro i j hij
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact hdisj i j hij
  obtain ⟨hT⟩ := nonempty_isColimit_cofanMk_of (fun i => (U i).ι) hcover hpair
  refine ⟨Cofan.IsColimit.desc hT (fun i => v i ≫ Sigma.ι H i),
    fun i => Cofan.IsColimit.fac hT _ i, ?_⟩
  intro u' hu'
  apply Cofan.IsColimit.hom_ext hT
  intro i
  exact (hu' i).trans (Cofan.IsColimit.fac hT (fun j => v j ≫ Sigma.ι H j) i).symm
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top
end ProofImplementation
