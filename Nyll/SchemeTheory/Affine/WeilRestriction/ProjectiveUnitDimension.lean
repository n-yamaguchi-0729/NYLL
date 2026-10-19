/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Dimension
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientGroupScheme

/-! Relative dimension of the concrete projective norm open and scalar quotient group scheme. -/

noncomputable section
universe u
open CategoryTheory

open AlgebraicGeometry Module

namespace SchemeTheory.Affine.ProjectiveUnitOpen

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- For an algebra of positive rank `n + 1`, its projective norm open has
relative dimension `n`. This is a property of the actual constructed open
scheme and does not presuppose any quotient representation theorem. -/
theorem smoothOfRelativeDimension_toBase : SmoothOfRelativeDimension n (toBase b) := by
  have : SmoothOfRelativeDimension n (ProjSpace.π R n) :=
    ProjSpace.smoothOfRelativeDimension_π R n
  change SmoothOfRelativeDimension n (projectiveι b ≫ ProjSpace.π R n)
  simpa only [Nat.zero_add] using
    smoothOfRelativeDimension_comp 0 n (projectiveι b) (ProjSpace.π R n)

end SchemeTheory.Affine.ProjectiveUnitOpen

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The actual scalar quotient of units of an algebra of rank `n + 1`
is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_scalarQuotientCommGroupScheme :
    SmoothOfRelativeDimension n (scalarQuotientCommGroupScheme b).X.hom := by
  rw [scalarQuotientCommGroupScheme_toBase]
  exact ProjectiveUnitOpen.smoothOfRelativeDimension_toBase b

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
