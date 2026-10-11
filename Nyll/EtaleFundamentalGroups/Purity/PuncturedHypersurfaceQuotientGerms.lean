/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceGerms
import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceNeighborhoodDiagram
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumQuotient
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitModels
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitStages
import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Whiskering
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Restriction of neighbourhood germs to the actual quotient puncture

The target in Stacks Project, Lemma 58.22.1 is the punctured spectrum of
`R / (f)`. The previously constructed neighbourhood cone uses the pullback
of `Spec (R / (f))` to the puncture of `Spec R`. The cartesian square of the
actual quotient morphism gives an isomorphism between these schemes,
compatible with both projections.

Base change through that isomorphism gives the restriction functor with
the original target. Its restriction to each stage is naturally the usual
pullback along the actual map from the quotient puncture. Faithfulness is
inherited from the proved geometric shrinking argument, without a new
faithfulness or comparison hypothesis.

Source: https://stacks.math.columbia.edu/tag/0BLN
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.PuncturedHypersurface

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable (R : Type u) [CommRing R] [IsLocalRing R] (f : R)
  (hf : f ∈ IsLocalRing.maximalIdeal R)

private theorem quotient_isLocalRing : IsLocalRing (R ⧸ Ideal.span {f}) := by
  have hI : Ideal.span {f} ≤ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf
  have : Nontrivial (R ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
    Ideal.Quotient.mk_surjective

/-- The punctured spectrum of the actual quotient is the hypersurface
pullback used in the neighbourhood cone. -/
def quotientPunctureIso :
    let : IsLocalRing (R ⧸ Ideal.span {f}) := quotient_isLocalRing R f hf
    Scheme.puncturedSpectrum (R ⧸ Ideal.span {f}) ≅ puncture R f := by
  intro hLocal
  exact (Scheme.puncturedSpectrumQuotientMorphism_isPullback R (Ideal.span {f})
    ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf)).isoPullback

/-- The comparison is over the original punctured local spectrum. -/
theorem quotientPunctureIso_hom_fst :
    let : IsLocalRing (R ⧸ Ideal.span {f}) := quotient_isLocalRing R f hf
    (quotientPunctureIso R f hf).hom ≫
        pullback.fst (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f) =
      Scheme.puncturedSpectrumQuotientMorphism R (Ideal.span {f})
        ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf) := by
  intro hLocal
  exact (Scheme.puncturedSpectrumQuotientMorphism_isPullback R (Ideal.span {f})
    ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf)).isoPullback_hom_fst

/-- The comparison also preserves the inclusion into the quotient spectrum. -/
theorem quotientPunctureIso_hom_snd :
    let : IsLocalRing (R ⧸ Ideal.span {f}) := quotient_isLocalRing R f hf
    (quotientPunctureIso R f hf).hom ≫
        pullback.snd (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f) =
      Scheme.puncturedSpectrumInclusion (R ⧸ Ideal.span {f}) := by
  intro hLocal
  exact (Scheme.puncturedSpectrumQuotientMorphism_isPullback R (Ideal.span {f})
    ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf)).isoPullback_hom_snd

/-- Restriction of neighbourhood germs to the literal punctured spectrum
of the quotient by the original equation. -/
def restrictionToQuotientPuncture :
    let : IsLocalRing (R ⧸ Ideal.span {f}) := quotient_isLocalRing R f hf
    (InverseLimitModel.cartesian (diagram R f)).Localization ⥤
      FiniteEtale (Scheme.puncturedSpectrum (R ⧸ Ideal.span {f})) := by
  intro hLocal
  exact InverseLimitModel.localizedBaseChange (diagram R f) (cone R f) ⋙
    FiniteEtale.pullback (quotientPunctureIso R f hf).hom

/-- On each actual neighbourhood, the germ restriction agrees naturally
with pullback along the map from the original quotient puncture. -/
def stageRestrictionToQuotientPunctureIso
    (i : (OrderDual (Neighborhood R f))ᵒᵖ) :
    let : IsLocalRing (R ⧸ Ideal.span {f}) := quotient_isLocalRing R f hf
    InverseLimitModel.localizedStageInclusion (diagram R f) i ⋙
        restrictionToQuotientPuncture R f hf ≅
      FiniteEtale.pullback
        ((quotientPunctureIso R f hf).hom ≫ projection R f i.unop) := by
  intro hLocal
  let F : FiniteEtale ((diagram R f).obj i) ⥤
      (InverseLimitModel.cartesian (diagram R f)).Localization :=
    InverseLimitModel.localizedStageInclusion (diagram R f) i
  let G : (InverseLimitModel.cartesian (diagram R f)).Localization ⥤
      FiniteEtale (puncture R f) :=
    InverseLimitModel.localizedBaseChange (diagram R f) (cone R f)
  let q : Scheme.puncturedSpectrum (R ⧸ Ideal.span {f}) ⟶ puncture R f :=
    (quotientPunctureIso R f hf).hom
  have hstage : F ⋙ G = FiniteEtale.pullback (projection R f i.unop) := by
    calc
      F ⋙ G = InverseLimitModel.stageInclusion (diagram R f) i ⋙
          ((InverseLimitModel.cartesian (diagram R f)).Q ⋙ G) :=
        Functor.assoc (InverseLimitModel.stageInclusion (diagram R f) i)
          (InverseLimitModel.cartesian (diagram R f)).Q G
      _ = InverseLimitModel.stageInclusion (diagram R f) i ⋙
          InverseLimitModel.baseChange (diagram R f) (cone R f) :=
        congrArg (fun H ↦ InverseLimitModel.stageInclusion (diagram R f) i ⋙ H)
          (InverseLimitModel.q_comp_localizedBaseChange (diagram R f) (cone R f))
      _ = FiniteEtale.pullback (projection R f i.unop) :=
        InverseLimitModel.stageInclusion_comp_baseChange (diagram R f) (cone R f) i
  exact (Functor.associator F G (FiniteEtale.pullback q)).symm ≪≫
    isoWhiskerRight (eqToIso hstage) (FiniteEtale.pullback q) ≪≫
    (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      q (projection R f i.unop) (q ≫ projection R f i.unop) rfl).symm

/-- The restriction from all neighbourhood germs to the punctured spectrum
of `R / (f)` is faithful under the original local Noetherian hypotheses of
Stacks 58.22.1. The concrete target comparison is constructed above. -/
theorem restrictionToQuotientPuncture_faithful [IsNoetherianRing R] :
    (restrictionToQuotientPuncture R f hf).Faithful := by
  have : (InverseLimitModel.localizedBaseChange (diagram R f) (cone R f)).Faithful :=
    restriction_faithful R f hf
  have : (FiniteEtale.pullback (quotientPunctureIso R f hf).hom).Faithful :=
    pullback_faithful_of_isDominant (quotientPunctureIso R f hf).hom
  exact Functor.Faithful.comp _ _

end AlgebraicGeometry.FiniteEtale.PuncturedHypersurface
