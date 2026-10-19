/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ExactSequence
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # The universal property of the actual norm-boundary kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- The concrete norm quotient is the identity kernel in the category of actual schemes
over the field. Its universal property follows from the proved representation and exactness. -/
def modulusNormBoundaryIsKernel :
    IsLimit (Fork.ofι (modulusNormBoundary c D hd).hom.hom.hom
      ((modulusNormBoundary_condition c D hd).trans
        (MonObj.comp_one (modulusNormBoundary c D hd).hom.hom.hom).symm)) := by
  apply Fork.IsLimit.ofExistsUnique
  intro s
  have hs : s.ι ≫ (groupProjection c D).hom.hom.hom = 1 :=
    s.condition.trans (MonObj.comp_one s.ι)
  obtain ⟨a, ha⟩ := (Set.ext_iff.mp (modulusNormBoundary_range D hd s.pt) s.ι).mpr hs
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply (modulusUnitQuotientRepresentable D hd).homEquiv.injective
  apply (CommGrpCat.mono_iff_injective
    ((modulusNormBoundarySheaf D).hom.app (op s.pt))).mp inferInstance
  rw [← modulusNormBoundary_homEquiv c D hd, ← modulusNormBoundary_homEquiv c D hd]
  exact congrArg (groupRepresentable c D).homEquiv (hb.trans ha.symm)

end AlgebraicGeometry.GeneralizedJacobian
