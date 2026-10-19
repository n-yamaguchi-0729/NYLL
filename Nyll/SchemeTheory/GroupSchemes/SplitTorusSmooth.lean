/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.SplitTorus
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Smooth.Basic

/-! # Smoothness of the actual split torus

The integral character algebra is an iterated Laurent polynomial algebra. Each
Laurent variable is obtained by localizing a polynomial algebra at its variable.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Polynomial LaurentPolynomial

namespace AlgebraicGeometry.GroupSchemes

variable (R : Type u) [CommRing R]

/-- The first integral character supplies a Laurent polynomial coordinate. -/
def splitTorusAlgebraSucc (r : ℕ) :
    splitTorusAlgebra R (r + 1) ≃ₐ[R] (splitTorusAlgebra R r)[T;T⁻¹] :=
  (AddMonoidAlgebra.domCongr R R
    (Fin.consLinearEquiv ℤ (fun _ : Fin (r + 1) => ℤ)).toAddEquiv.symm).trans
      (AddMonoidAlgebra.curryAlgEquiv R)

private theorem laurent_smooth (A : Type u) [CommRing A] :
    Algebra.Smooth A A[T;T⁻¹] := by
  have : IsScalarTower A A[X] A[T;T⁻¹] :=
    IsScalarTower.of_algebraMap_eq fun a => by
      exact (Polynomial.toLaurentAlg (R := A)).commutes a |>.symm
  have : Algebra.Smooth A A[X] := {}
  have : Algebra.Smooth A[X] A[T;T⁻¹] :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : A[X])
  exact Algebra.Smooth.comp A A[X] A[T;T⁻¹]

/-- The integral character algebra is smooth over its coefficient ring. -/
theorem splitTorusAlgebra_smooth (r : ℕ) : Algebra.Smooth R (splitTorusAlgebra R r) := by
  induction r with
  | zero =>
    have : Algebra.Smooth R R := {}
    exact Algebra.Smooth.of_equiv
      (AddMonoidAlgebra.bialgEquivOfSubsingleton (R := R) (Fin 0 → ℤ)).toAlgEquiv.symm
  | succ r ih =>
    have : Algebra.Smooth R (splitTorusAlgebra R r) := ih
    have : Algebra.Smooth (splitTorusAlgebra R r) (splitTorusAlgebra R r)[T;T⁻¹] :=
      laurent_smooth (splitTorusAlgebra R r)
    have : Algebra.Smooth R (splitTorusAlgebra R r)[T;T⁻¹] :=
      Algebra.Smooth.comp R (splitTorusAlgebra R r) (splitTorusAlgebra R r)[T;T⁻¹]
    exact Algebra.Smooth.of_equiv (splitTorusAlgebraSucc R r).symm

/-- Every actual split torus is smooth over its base ring. -/
instance splitTorus_smooth (r : ℕ) : Smooth (splitTorus R r).X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (splitTorusAlgebra R r))))
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr (splitTorusAlgebra_smooth R r)

end AlgebraicGeometry.GroupSchemes
