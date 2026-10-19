/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.InternalHom
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Restricting a global-sections functor to coefficient spectra

The relative Gamma--Spec counit identifies the actual coefficient algebra
of a spectrum with the original algebra, naturally. Composing this counit
with an algebra-valued test functor retains its given scalar action.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory

namespace SchemeTheory.Affine

variable (R : CommRingCat.{u})

/-- The natural relative Gamma--Spec comparison, with the coefficient actions retained. -/
def relativeSpectrumSectionsIso :
    specOverFunctor R ⋙ AlgebraicGeometry.algΓ R ≅ 𝟭 (CommAlgCat.{u} R)ᵒᵖ := by
  have : (AlgebraicGeometry.algSpec R).Full :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := R)).full
  have : (AlgebraicGeometry.algSpec R).Faithful :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := R)).faithful
  let e : AlgebraicGeometry.algSpec R ⋙ AlgebraicGeometry.algΓ R ≅
      𝟭 (CommAlgCat.{u} R)ᵒᵖ := asIso (AlgebraicGeometry.algΓAlgSpecAdjunction R).counit
  exact e

variable {V : Type v} [Category.{w} V] (F : CommAlgCat.{u} R ⥤ V)

/-- Evaluate an algebra functor on relative global sections, then restrict to spectra. -/
def relativeSectionsSpectrumRestrictionIso :
    (specOverFunctor R).op ⋙ ((AlgebraicGeometry.algΓ R).op ⋙
      (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ F) ≅
        (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ F :=
  (Functor.associator (specOverFunctor R).op (AlgebraicGeometry.algΓ R).op
    ((opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ F)).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op (relativeSpectrumSectionsIso R).symm)
        ((opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ F) ≪≫
          Functor.leftUnitor _

end SchemeTheory.Affine
