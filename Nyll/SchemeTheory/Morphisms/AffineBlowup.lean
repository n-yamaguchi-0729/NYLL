/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.GradedReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The affine blowup as Proj of the actual Rees algebra

The degree-zero coefficient isomorphism gives the structure map over Spec R.
For a finitely generated ideal the Rees algebra is of finite type over this
actual degree-zero part, so the existing Proj properness theorem applies.
No Noetherianity, regularity of the ideal, or freeness of its powers is used.
This is the Proj construction of Stacks Project, Section 31.33; its universal
property and gluing over nonaffine bases are separate subsequent results.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The affine blowup is Proj of the graded polynomial Rees subalgebra. -/
def affineBlowup : Scheme.{u} := Proj (ReesAlgebra.homogeneousPart I)

/-- The actual structure map of the affine blowup to the coefficient spectrum. -/
def affineBlowupMap : affineBlowup I ⟶ Spec (.of R) :=
  Proj.toSpecZero (ReesAlgebra.homogeneousPart I) ≫
    Spec.map (RingEquiv.toCommRingCatIso (R := R)
      (S := ↥(ReesAlgebra.homogeneousPart I 0)) (ReesAlgebra.degreeZeroEquiv I)).hom

/-- Blowing up a finitely generated ideal in an affine scheme is proper. -/
theorem affineBlowupMap_isProper (hI : I.FG) : IsProper (affineBlowupMap I) := by
  have : Algebra.FiniteType (ReesAlgebra.homogeneousPart I 0) (reesAlgebra I) :=
    ReesAlgebra.finiteType_degreeZero I hI
  have : IsProper (Proj.toSpecZero (ReesAlgebra.homogeneousPart I)) := inferInstance
  let e : CommRingCat.of R ≅ CommRingCat.of ↥(ReesAlgebra.homogeneousPart I 0) :=
    (ReesAlgebra.degreeZeroEquiv I).toCommRingCatIso
  have : IsProper (Spec.map e.hom) := inferInstance
  unfold affineBlowupMap
  exact inferInstanceAs
    (IsProper (Proj.toSpecZero (ReesAlgebra.homogeneousPart I) ≫ Spec.map e.hom))

end AlgebraicGeometry
