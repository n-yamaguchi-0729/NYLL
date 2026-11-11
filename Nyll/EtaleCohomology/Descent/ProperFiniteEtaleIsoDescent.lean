/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.ProperFiniteEtaleNativeOverlap
public import Nyll.EtaleFundamentalGroups.FiniteEtale.CanonicalDescent

/-!
# Descent of the original isomorphism under a proper surjection

An isomorphism of the actual pullbacks descends uniquely when it respects
the canonical overlap maps. The original isomorphism is recovered exactly.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.Cohomology

universe u

namespace EtaleCohomology.SetSheafDescent

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- A compatible isomorphism of the actual finite étale pullbacks descends
uniquely along the original proper surjection. -/
theorem existsUnique_iso_of_proper_pullback
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsProper q] [Surjective q]
    (V₁ V₂ : FiniteEtale X)
    (ρ : (FiniteEtale.pullback q).obj V₁ ≅ (FiniteEtale.pullback q).obj V₂)
    (hρ :
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) (pullback.fst q q) q).hom.app V₁) ≫
          (FiniteEtale.pullback (pullback.fst q q)).map ρ.hom ≫
            (FiniteEtale.canonicalPullbackDescentIso q V₂).hom =
        ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) (pullback.snd q q) q
            (pullback.fst q q ≫ q) pullback.condition).hom.app V₁) ≫
          (FiniteEtale.pullback (pullback.snd q q)).map ρ.hom) :
    ∃! τ : V₁ ≅ V₂, (FiniteEtale.pullback q).map τ.hom = ρ.hom := by
  let W := (FiniteEtale.pullback q).obj V₂
  let θ := FiniteEtale.canonicalPullbackDescentIso q V₂
  have htriple :
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        finiteEtalePairIso q W θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      finiteEtalePairIso q W θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q) :=
    FiniteEtale.canonicalPullbackDescentIso_cocycle q V₂
      (FiniteEtale.radicialTripleFirst q) (FiniteEtale.radicialTripleSecond q)
      (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_second q)
      (FiniteEtale.radicialTriple_second_third q)
  have h₁ := sheaf_overlap_of_native_overlap q V₁ W θ ρ.hom hρ
  have h₂ := sheaf_overlap_of_native_overlap q V₂ W θ (𝟙 W)
    (FiniteEtale.canonicalPullbackDescentIso_identity_overlap q V₂)
  obtain ⟨τ, hτ, huniq⟩ := existsUnique_finiteEtale_iso_of_descent
    q W θ htriple V₁ V₂ ρ (Iso.refl W) h₁ h₂
  refine ⟨τ, ?_, ?_⟩
  · exact (Category.comp_id _).symm.trans hτ
  · intro σ hσ
    exact huniq σ ((Category.comp_id _).trans hσ)

end EtaleCohomology.SetSheafDescent
