/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Recovery of actual polynomial matrix cokernels under base change

Pullback is a left adjoint, so it carries the original cokernel to the
cokernel of the original pulled-back morphism. The proved coefficient
base-change square for polynomial matrices identifies this with the
native cokernel of the matrix with mapped coefficients.

The resulting isomorphism commutes with the actual cokernel projections.
No flatness assumption on the change of coefficients is required.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

private def pullbackCokernelIsoOfSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {M' N' : X.Modules} (a : M ⟶ N) (b : M' ⟶ N')
    (p : (Scheme.Modules.pullback f).obj M ≅ M')
    (q : (Scheme.Modules.pullback f).obj N ≅ N')
    (h : (Scheme.Modules.pullback f).map a ≫ q.hom = p.hom ≫ b) :
    (Scheme.Modules.pullback f).obj (cokernel a) ≅ cokernel b :=
  PreservesCokernel.iso (Scheme.Modules.pullback f) a ≪≫
    cokernel.mapIso ((Scheme.Modules.pullback f).map a) b p q h

private theorem pullbackCokernelIsoOfSquare_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {M' N' : X.Modules} (a : M ⟶ N) (b : M' ⟶ N')
    (p : (Scheme.Modules.pullback f).obj M ≅ M')
    (q : (Scheme.Modules.pullback f).obj N ≅ N')
    (h : (Scheme.Modules.pullback f).map a ≫ q.hom = p.hom ≫ b) :
    (Scheme.Modules.pullback f).map (cokernel.π a) ≫
        (pullbackCokernelIsoOfSquare f a b p q h).hom = q.hom ≫ cokernel.π b := by
  change (Scheme.Modules.pullback f).map (cokernel.π a) ≫
    ((PreservesCokernel.iso (Scheme.Modules.pullback f) a).hom ≫
      (cokernel.mapIso ((Scheme.Modules.pullback f).map a) b p q h).hom) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
  (I J : Type u) [Finite J] (d : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The actual pulled-back cokernel is the native cokernel of the
original polynomial matrix with coefficients changed to the new ring. -/
def polynomialMatrixCokernelBaseChangeIso (m : I → J → 𝒜R d) :
    (Scheme.Modules.pullback (map R A n)).obj
        (cokernel (polynomialMatrixHom R n I J d m)) ≅
      cokernel (polynomialMatrixHom A n I J d
        (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j))) :=
  pullbackCokernelIsoOfSquare (map R A n)
    (polynomialMatrixHom R n I J d m)
    (polynomialMatrixHom A n I J d
      (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j)))
    (pullbackFreeIso (map R A n) I) (freeTwistBaseChangeIso R A n J d)
    (polynomialMatrixHom_baseChange R A n I J d m)

/-- The comparison retains the actual quotient projection from the
pulled-back free twist to the original matrix cokernel. -/
theorem polynomialMatrixCokernelBaseChangeIso_projection (m : I → J → 𝒜R d) :
    (Scheme.Modules.pullback (map R A n)).map
        (cokernel.π (polynomialMatrixHom R n I J d m)) ≫
      (polynomialMatrixCokernelBaseChangeIso R A n I J d m).hom =
        (freeTwistBaseChangeIso R A n J d).hom ≫
          cokernel.π (polynomialMatrixHom A n I J d
            (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j))) :=
  pullbackCokernelIsoOfSquare_projection (map R A n)
    (polynomialMatrixHom R n I J d m)
    (polynomialMatrixHom A n I J d
      (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j)))
    (pullbackFreeIso (map R A n) I) (freeTwistBaseChangeIso R A n J d)
    (polynomialMatrixHom_baseChange R A n I J d m)

end AlgebraicGeometry.ProjSpace
