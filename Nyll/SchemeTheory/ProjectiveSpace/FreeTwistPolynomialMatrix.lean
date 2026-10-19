/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Tensor.FiniteFreeSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafGlobalSections
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPresentation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Logic.Equiv.Basic

/-!
# Actual polynomial matrices presenting coherent projective sheaves

A morphism from a free sheaf is determined by its original global
generator images. Sections of a finite free twist are actual tuples
of twisting-sheaf sections, and each of those sections is represented
by a unique homogeneous polynomial. These three comparisons give a
bijection between actual presenting morphisms and polynomial matrices.

The inverse constructs the original native sheaf morphism from the
matrix. Its evaluation formula retains each original free generator.
Applying the comparison to the constructed finite cokernel presentation
gives a genuine homogeneous polynomial matrix whose native cokernel is
a twist of the given coherent sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "X" => Proj 𝒜

section Matrix

variable (I J : Type u) [hJ : Finite J] (d : ℕ)

/-- A morphism into a finite free degree-`d` twist is exactly a
matrix of homogeneous degree-`d` polynomials. The first matrix index
is the source generator, and the second index is the target coordinate. -/
def freeTwistPolynomialMatrixEquiv :
    ((show (X).Modules from SheafOfModules.free I) ⟶
      (show (X).Modules from SheafOfModules.free J) ⊗
        (twistingSheaf R n).tensorPow d) ≃ (I → J → 𝒜 d) := by
  let L : (X).Modules := (twistingSheaf R n).tensorPow d
  let T : (X).Modules := (show (X).Modules from SheafOfModules.free J) ⊗ L
  let e : Γ(T, ⊤) ≃ (J → 𝒜 d) :=
    (finiteFreeTensorSectionsEquiv J ⊤ (π R n) L).toEquiv.trans
      (Equiv.piCongrRight (fun _ : J =>
        (polynomialTwistingSectionLinearEquiv R n d).symm.toEquiv))
  exact (freeHomTopSectionsEquiv T I).trans (Equiv.piCongrRight (fun _ : I => e))

/-- Each matrix entry is obtained from the original generator image
by the actual finite-free coordinate map and polynomial recovery. -/
theorem freeTwistPolynomialMatrixEquiv_apply
    (φ : (show (X).Modules from SheafOfModules.free I) ⟶
      (show (X).Modules from SheafOfModules.free J) ⊗
        (twistingSheaf R n).tensorPow d) (i : I) (j : J) :
    freeTwistPolynomialMatrixEquiv R n I J d φ i j =
      (polynomialTwistingSectionLinearEquiv R n d).symm
        (finiteFreeTensorSectionsEquiv J ⊤ (π R n) ((twistingSheaf R n).tensorPow d)
          (φ.app ⊤ ((SheafOfModules.freeSection (R := (X).ringCatSheaf) i).val (op ⊤)))
            j) := rfl

/-- The actual native sheaf morphism constructed from a homogeneous
polynomial matrix. -/
def polynomialMatrixHom (m : I → J → 𝒜 d) :
    (show (X).Modules from SheafOfModules.free I) ⟶
      (show (X).Modules from SheafOfModules.free J) ⊗
        (twistingSheaf R n).tensorPow d :=
  (freeTwistPolynomialMatrixEquiv R n I J d).symm m

/-- Extracting the polynomial matrix of the constructed morphism
returns exactly the original matrix. -/
theorem polynomialMatrixHom_matrix (m : I → J → 𝒜 d) :
    freeTwistPolynomialMatrixEquiv R n I J d (polynomialMatrixHom R n I J d m) = m :=
  (freeTwistPolynomialMatrixEquiv R n I J d).apply_symm_apply m

/-- Reconstructing the morphism from its actual matrix returns the
original native sheaf morphism. -/
theorem polynomialMatrixHom_of_hom
    (φ : (show (X).Modules from SheafOfModules.free I) ⟶
      (show (X).Modules from SheafOfModules.free J) ⊗
        (twistingSheaf R n).tensorPow d) :
    polynomialMatrixHom R n I J d (freeTwistPolynomialMatrixEquiv R n I J d φ) = φ :=
  (freeTwistPolynomialMatrixEquiv R n I J d).symm_apply_apply φ

/-- Each actual free generator is sent to the tuple of original
polynomial sections specified by its matrix column. -/
theorem polynomialMatrixHom_generator (m : I → J → 𝒜 d) (i : I) (j : J) :
    finiteFreeTensorSectionsEquiv J ⊤ (π R n) ((twistingSheaf R n).tensorPow d)
        ((polynomialMatrixHom R n I J d m).app ⊤
          ((SheafOfModules.freeSection (R := (X).ringCatSheaf) i).val (op ⊤))) j =
      polynomialTwistingSection R n d (m i j) := by
  let e := polynomialTwistingSectionLinearEquiv R n d
  let z := finiteFreeTensorSectionsEquiv J ⊤ (π R n) ((twistingSheaf R n).tensorPow d)
    ((polynomialMatrixHom R n I J d m).app ⊤
      ((SheafOfModules.freeSection (R := (X).ringCatSheaf) i).val (op ⊤))) j
  have h : e.symm z = m i j :=
    congrFun (congrFun (polynomialMatrixHom_matrix R n I J d m) i) j
  exact (e.apply_symm_apply z).symm.trans
    ((congrArg (fun p : 𝒜 d => e p) h).trans
      (polynomialTwistingSectionLinearEquiv_apply R n d (m i j)))

end Matrix

/-- A native finite-type quasicoherent sheaf on projective space
has a twist presented by an actual finite homogeneous polynomial matrix. -/
theorem exists_homogeneous_polynomial_matrix_presentation [IsNoetherianRing R]
    (F : (X).Modules)
    [SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := (X).ringCatSheaf) F] :
    ∃ a b : ℕ, ∃ I J : Type u, ∃ _ : Finite I, ∃ hJ : Finite J,
      ∃ m : I → J → 𝒜 b,
        Nonempty (cokernel (polynomialMatrixHom R n I J (hJ := hJ) b m) ≅
          F ⊗ (twistingSheaf R n).tensorPow (a + b)) := by
  obtain ⟨a, b, I, J, hI, hJ, φ, e⟩ := exists_twisting_finite_cokernel_presentation R n F
  have : Finite J := hJ
  refine ⟨a, b, I, J, hI, hJ, freeTwistPolynomialMatrixEquiv R n I J b φ, ?_⟩
  rw [polynomialMatrixHom_of_hom]
  exact e

end AlgebraicGeometry.ProjSpace
