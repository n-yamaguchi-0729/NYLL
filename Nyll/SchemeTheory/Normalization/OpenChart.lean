/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SourceIso
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The actual local normalization on an open chart

Suppose a cover is given on an open `U` of an ambient scheme `X`.
On another open chart `V`, first restrict `U`, then pull back the original
cover to that intersection, and normalize over `V`. This is the actual
restriction to `V` of the one global relative normalization over `X`.

The source comparison is constructed from pullback pasting. Smooth base
change of relative normalization then gives the isomorphism. It preserves
both the original generic-cover map and the projection to the chart.
Consequently the normalization models used on overlapping affine charts
are restrictions of the same scheme, without assuming a gluing comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {Z U X V : Scheme.{u}}
  (p : Z ⟶ U) [QuasiCompact p] [QuasiSeparated p]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (v : V ⟶ X) [IsOpenImmersion v]

/-- Normalize the actual cover pulled back to the intersection with an
open chart. Its normalization is the chart restriction of the global one. -/
def normalizationOpenChartIso :
    (pullback.snd p (pullback.fst j v) ≫ pullback.snd j v).normalization ≅
      pullback (p ≫ j).fromNormalization v :=
  normalizationSourceIso
    (pullback.snd p (pullback.fst j v) ≫ pullback.snd j v)
    (pullback.snd (p ≫ j) v) (pullbackRightPullbackFstIso j v p)
    (pullbackRightPullbackFstIso_hom_snd j v p) ≪≫
      asIso ((p ≫ j).normalizationPullback v)

/-- The local-to-global normalization comparison is over the original
open chart. -/
@[reassoc]
theorem normalizationOpenChartIso_hom_snd :
    (normalizationOpenChartIso p j v).hom ≫ pullback.snd (p ≫ j).fromNormalization v =
      (pullback.snd p (pullback.fst j v) ≫ pullback.snd j v).fromNormalization := by
  simp only [normalizationOpenChartIso, Iso.trans_hom, Category.assoc, asIso_hom,
    normalizationPullback_snd, normalizationSourceIso_hom_fromNormalization]

/-- The comparison also retains the original cover, so it identifies
the actual extension of that cover on each chart. -/
@[reassoc]
theorem toNormalization_normalizationOpenChartIso_hom_fst :
    (pullback.snd p (pullback.fst j v) ≫ pullback.snd j v).toNormalization ≫
      (normalizationOpenChartIso p j v).hom ≫ pullback.fst (p ≫ j).fromNormalization v =
        pullback.fst p (pullback.fst j v) ≫ (p ≫ j).toNormalization := by
  simp only [normalizationOpenChartIso, Iso.trans_hom, Category.assoc, asIso_hom,
    toNormalization_normalizationSourceIso_hom_assoc,
    toNormalization_normalizationPullback_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]

end AlgebraicGeometry.Scheme.Hom
