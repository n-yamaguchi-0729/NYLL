/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Specified tensor inverse comparisons

These comparisons retain the supplied evaluations and the explicit associator,
braiding and unitor compositions used by change of rigidification.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]

/-- Compare specified tensor inverses through the original evaluation isomorphisms. -/
def tensorInverseIso {X X' Q Q' : 𝒞} (eX : X ≅ X') (hQ : X ⊗ Q ≅ 𝟙_ 𝒞)
    (hQ' : X' ⊗ Q' ≅ 𝟙_ 𝒞) : Q ≅ Q' :=
  (ρ_ Q).symm ≪≫ whiskerLeftIso Q hQ'.symm ≪≫ (α_ Q X' Q').symm ≪≫
    whiskerRightIso ((β_ Q X') ≪≫ whiskerRightIso eX.symm Q ≪≫ hQ) Q' ≪≫ λ_ Q'

/-- Transport the specified inverse evaluation along the given isomorphism. -/
def tensorInverseOfIso {X Y Q : 𝒞} (eX : X ≅ Y) (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) : Y ⊗ Q ≅ 𝟙_ 𝒞 :=
  whiskerRightIso eX.symm Q ≪≫ hQ

end CategoryTheory.MonoidalCategory
