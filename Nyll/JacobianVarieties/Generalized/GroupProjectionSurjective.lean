/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.ModulusForgetfulSurjectivity
import Nyll.SchemeTheory.Topology.RepresentedFppfSurjective

/-! # The arbitrary-field projection is surjective on actual scheme points -/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- Forgetting rigidification is surjective as an actual scheme morphism over every field. -/
theorem groupProjection_surjective : Surjective (groupProjection c D).hom.hom.hom.left := by
  have : Sheaf.IsLocallySurjective (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) :=
    forgetModulusZeroGroupSheaf_locallySurjective D
  exact surjective_of_represented_fppf_locallySurjective
    (Functor.whiskerRight (forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom
      (forget CommGrpCat.{u + 1}))
    (groupRepresentable c D) (ordinaryGroupRepresentable c)
    (groupProjection c D).hom.hom.hom (groupProjection_homEquiv c D)

end AlgebraicGeometry.GeneralizedJacobian
