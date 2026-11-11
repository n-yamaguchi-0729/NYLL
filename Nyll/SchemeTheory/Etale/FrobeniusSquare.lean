/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.Frobenius
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The cartesian Frobenius square of an étale morphism

The actual relative Frobenius isomorphism identifies the Frobenius
naturality square with the pullback square. This retains the original
schemes and maps for subsequent base-change constructions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [Fintype k] {U X : Scheme.{u}}
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]

/-- Frobenius naturality is a cartesian square for every étale morphism. -/
theorem finiteFieldFrobenius_isPullback (j : U ⟶ X) [AlgebraicGeometry.Etale j] :
    IsPullback (U.finiteFieldFrobenius k) j j (X.finiteFieldFrobenius k) := by
  have : IsIso (relativeFiniteFieldFrobenius k j) := relativeFiniteFieldFrobenius_isIso k j
  exact IsPullback.of_iso_pullback
    ⟨finiteFieldFrobenius_naturality U k X j⟩
    (asIso (relativeFiniteFieldFrobenius k j))
    (relativeFiniteFieldFrobenius_fst k j) (relativeFiniteFieldFrobenius_snd k j)

end AlgebraicGeometry.Scheme
