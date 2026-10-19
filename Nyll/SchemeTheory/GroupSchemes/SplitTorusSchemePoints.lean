/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.SplitTorusPoints
import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints

/-! # Split-torus points on arbitrary test schemes

The relative Gamma--Spec adjunction identifies the actual split-torus group of
points with tuples of global units, including for nonaffine test schemes.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GroupSchemes

variable (R : Type u) [CommRing R]

local instance : (algSpec (CommRingCat.of R)).Monoidal :=
  (braidedAlgSpec (R := CommRingCat.of R)).toMonoidal

/-- Points of the actual split torus on any test scheme are tuples of global units. -/
def splitTorusPointEquiv (r : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (splitTorus R r).X) ≃*
      (Fin r → ((algΓ (CommRingCat.of R)).obj T).unopˣ) :=
  ((algΓAlgSpecAdjunction (CommRingCat.of R)).homMulEquiv T
    (op (CommAlgCat.of R (splitTorusAlgebra R r)))).symm.trans
      ((characterAlgebraPointsEquiv R ((algΓ (CommRingCat.of R)).obj T).unop
        (Fin r → ℤ)).trans
        (latticeCharactersEquiv (((algΓ (CommRingCat.of R)).obj T).unopˣ) r))

/-- Coordinate functions are the images of the integral-character basis monomials. -/
theorem splitTorusPointEquiv_apply (r : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (splitTorus R r).X) (j : Fin r) :
    ↑(splitTorusPointEquiv R r T x j) =
      (((algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv T
        (op (CommAlgCat.of R (splitTorusAlgebra R r)))).symm x).unop.hom
          (AddMonoidAlgebra.single (Pi.single j 1) 1) :=
  congrArg Units.val (latticeCharactersEquiv_apply
    (((algΓ (CommRingCat.of R)).obj T).unopˣ) r
    (characterAlgebraPointsEquiv R ((algΓ (CommRingCat.of R)).obj T).unop
      (Fin r → ℤ)
      (((algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv T
        (op (CommAlgCat.of R (splitTorusAlgebra R r)))).symm x)) j)

/-- The global-unit description commutes with pullback on every test scheme. -/
theorem splitTorusPointEquiv_naturality (r : ℕ)
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x : T ⟶ (splitTorus R r).X) (j : Fin r) :
    splitTorusPointEquiv R r T' (f ≫ x) j =
      Units.map (((algΓ (CommRingCat.of R)).map f).unop.hom.toRingHom.toMonoidHom)
        (splitTorusPointEquiv R r T x j) := by
  apply Units.ext
  change ↑(splitTorusPointEquiv R r T' (f ≫ x) j) =
    ((algΓ (CommRingCat.of R)).map f).unop.hom
      (↑(splitTorusPointEquiv R r T x j))
  rw [splitTorusPointEquiv_apply, splitTorusPointEquiv_apply]
  exact congrArg
    (fun h : (algΓ (CommRingCat.of R)).obj T' ⟶
        op (CommAlgCat.of R (splitTorusAlgebra R r)) =>
      h.unop.hom (AddMonoidAlgebra.single (Pi.single j 1) 1))
    ((algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv_naturality_left_symm f x)

end AlgebraicGeometry.GroupSchemes
