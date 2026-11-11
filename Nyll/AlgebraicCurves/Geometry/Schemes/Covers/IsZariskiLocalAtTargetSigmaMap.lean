/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Nyll.SchemeTheory.Morphisms.SigmaPullback

/-!
# Is Zariski Local At Target sigma Map
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.IsZariskiLocalAtTarget_sigmaMap

universe u v

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (sigmaMk_mk Scheme.Hom IsZariskiLocalAtTarget Scheme sigmaι_eq_iff
  IsOpenImmersion sigmaOpenCover IsZariskiLocalAtTarget.of_openCover sigmaMk
  IsOpenImmersion.isPullback Scheme.Hom.comp_apply)

namespace SigmaMapU4

open _root_.AlgebraicGeometry


variable {σ : Type v} [Small.{u} σ] {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)

theorem sigmaMap_sigmaι_apply (i : σ) (x : X i) :
    (Limits.Sigma.map f) ((Limits.Sigma.ι X i) x) = (Limits.Sigma.ι Y i) (f i x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.Sigma.ι_map]


theorem isPullback_sigmaι_sigmaMap (j : σ) :
    IsPullback (f j) (Limits.Sigma.ι X j) (Limits.Sigma.ι Y j) (Limits.Sigma.map f) := by
  exact _root_.AlgebraicGeometry.isPullback_sigmaι_sigmaMap f j

end AlgebraicGeometry.SigmaMapU4

open AlgebraicGeometry.SigmaMapU4 in
theorem _root_.AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {σ : Type v} [Small.{u} σ] {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  exact (_root_.AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap_iff f P).mpr hf
end AlgebraicCurves.Geometry.Schemes.Proofs.IsZariskiLocalAtTarget_sigmaMap
end ProofImplementation
