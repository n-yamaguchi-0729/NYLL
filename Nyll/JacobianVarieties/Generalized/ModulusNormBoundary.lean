/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusKernelExactness
import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient

/-! # The concrete norm-open boundary and its actual fppf kernel image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open SchemeTheory.Affine AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- The proved group comparison from the actual norm-open functor to modulus units. -/
def modulusAlgebraUnitGroupSheafIso :
    ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D) ≅
      modulusUnitQuotientGroupSheaf (modulusCurveMap D ≫ c) := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  exact modulusUnitGroupSheafComparisonIso (modulusBaseMap D) ≪≫
    eqToIso (congrArg modulusUnitQuotientGroupSheaf (modulusCurveMap_toBase D).symm)

/-- The norm-open scalar boundary into the actual modulus Picard-zero sheaf. -/
def modulusNormBoundarySheaf :
    ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D) ⟶
      modulusPicardZeroGroupSheaf c (modulusCurveMap D) :=
  (modulusAlgebraUnitGroupSheafIso D).hom ≫ modulusUnitBoundarySheaf c (modulusCurveMap D)

/-- The actual norm-open boundary is a monomorphism of fppf group sheaves. -/
instance modulusNormBoundarySheaf_mono : Mono (modulusNormBoundarySheaf D) := by
  unfold modulusNormBoundarySheaf
  infer_instance

/-- The norm-open boundary has precisely the actual forgetful kernel as its image. -/
theorem modulusNormBoundarySheaf_range (T : Over (Spec (CommRingCat.of K))) :
    Set.range ((modulusNormBoundarySheaf D).hom.app (op T)).hom =
      {x | ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom x = 1} := by
  rw [← modulusUnitBoundarySheaf_range c (modulusCurveMap D) T]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨((modulusAlgebraUnitGroupSheafIso D).hom.hom.app (op T)).hom a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨((modulusAlgebraUnitGroupSheafIso D).inv.hom.app (op T)).hom a, ?_⟩
    exact congrArg ((modulusUnitBoundarySheaf c (modulusCurveMap D)).hom.app (op T)).hom
      (congrArg (fun f : modulusUnitQuotientGroupSheaf (modulusCurveMap D ≫ c) ⟶
          modulusUnitQuotientGroupSheaf (modulusCurveMap D ≫ c) =>
            (f.hom.app (op T)).hom a) (modulusAlgebraUnitGroupSheafIso D).inv_hom_id)

end AlgebraicGeometry.GeneralizedJacobian
