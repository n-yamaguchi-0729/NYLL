/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Descent.GlobalRepresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Matching on an actual fppf descent cover

The singleton cover used by effective descent is covering in the slice fppf
site. Consequently every actual fppf sheaf satisfies precisely the matching
condition required by the global representation construction.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]

/-- An fppf sheaf satisfies descent on the actual singleton cover `coverT`. -/
theorem isSheafFor_coverT_of_isSheaf
    (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) (T : Over S) :
    Presieve.IsSheafFor G (Presieve.singleton (coverT s T)) := by
  apply ((isSheaf_iff_isSheaf_of_type _ G).mp hG).isSheafFor
  rw [← Presieve.ofArrows_pUnit.{0}, ← Sieve.ofArrows,
    GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows,
    Sieve.ofArrows, Presieve.ofArrows_pUnit.{0}]
  exact Precoverage.generate_mem_toGrothendieck
    (pullback.fst T.hom s).singleton_mem_fppfPrecoverage

end AlgebraicGeometry.DescentAction
