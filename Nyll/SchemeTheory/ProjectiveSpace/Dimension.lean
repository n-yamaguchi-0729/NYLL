/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Smooth
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmooth

/-! Projective space has relative dimension equal to its number of affine chart coordinates. -/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective `n`-space is smooth of relative dimension `n` over every
commutative coefficient ring. -/
theorem smoothOfRelativeDimension_π (R : Type u) [CommRing R] (n : ℕ) :
    SmoothOfRelativeDimension n (π R n) := by
  have : IsZariskiLocalAtSource
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension n)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension n)
    (affineOpenCover R n).openCover
  change ∀ j : Fin (n + 1), SmoothOfRelativeDimension n
    (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j) (X_mem_one R n j) one_pos ≫ π R n)
  intro j
  rw [awayι_comp_π R n j,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
    (algebraMap R (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j)))
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have hcard : Nat.card {k : Fin (n + 1) // k ≠ j} = n :=
    (Nat.card_congr (finSuccAboveEquiv j)).symm.trans (Nat.card_fin n)
  have : Algebra.IsStandardSmoothOfRelativeDimension n R
      (MvPolynomial {k : Fin (n + 1) // k ≠ j} R) := by
    simpa only [hcard] using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial
      R {k : Fin (n + 1) // k ≠ j}
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv n
    (awayChartEquiv (S := R) n j)

end AlgebraicGeometry.ProjSpace
