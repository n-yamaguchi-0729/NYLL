/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.NatIso

/-! # Comparing successive transports with a direct transport

One comparison is formed from the actual object isomorphisms and the
isomorphism between the direct and composite functors.
-/

namespace CategoryTheory

/-- The comparison of two successive transports with a direct transport,
formed from the three actual object comparisons and the functor comparison. -/
def scalarTowerComparisonIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ C) (F₁ : A ⥤ B) (F₂ : B ⥤ C) (e : F ≅ F₁ ⋙ F₂)
    {P₀ : A} {P₁ : B} {P₂ P₃ : C}
    (p₁ : P₁ ≅ F₁.obj P₀) (p₂ : P₂ ≅ F₂.obj P₁) (p₀ : F.obj P₀ ≅ P₃) :
    P₂ ≅ P₃ :=
  p₂ ≪≫ F₂.mapIso p₁ ≪≫ (e.app P₀).symm ≪≫ p₀

end CategoryTheory
