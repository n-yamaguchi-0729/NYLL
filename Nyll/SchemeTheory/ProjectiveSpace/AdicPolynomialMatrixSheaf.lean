/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.ProjectiveSpace.AdicFreeTwistCokernel
public import Nyll.SchemeTheory.ProjectiveSpace.AdicFreeTwistHom
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeQuotient
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentCokernel
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialBaseChange
public import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
public import Nyll.SchemeTheory.ProjectiveSpace.PolynomialMatrixCokernel
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.HomogeneousPolynomialSystem
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Actual sheaves from compatible homogeneous polynomial matrices

A compatible system of fixed-degree homogeneous polynomial matrices
over the positive adic quotients has an actual matrix over the complete
coefficient ring. Form the native sheaf cokernel of that lifted matrix.
Its pullback to every quotient is the original native matrix cokernel,
with the original quotient projections retained.

The constructed sheaf is quasicoherent and of finite type when the
target matrix index is finite. The input here is the actual compatible
matrix system. Producing such uniformly sized compatible presentations
for an arbitrary formal coherent sheaf is a separate geometric step.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (a : Ideal R) [IsAdicComplete a R]
  (n : ℕ) (I J : Type u) (d : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
variable (m : (k : ℕ) → I → J →
    MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (R ⧸ adicFreeTwistHomStageIdeal R a k) d)
  (hm : ∀ (k : ℕ) (i : I) (j : J),
    MvPolynomial.map (Ideal.Quotient.factorPow a (Nat.le_succ (k + 1)))
        (m (k + 1) i j).val = (m k i j).val)

/-- The actual homogeneous matrix obtained by lifting every
compatible coefficient and retaining the original matrix indices. -/
def adicPolynomialMatrix : I → J → 𝒜 d := fun i j =>
  MvPolynomial.homogeneousAdicLift a d (fun k => m k i j) (fun k => hm k i j)

/-- The original geometric coefficient map reduces the lifted
matrix to the originally supplied matrix at every adic stage. -/
theorem adicPolynomialMatrix_reduction (k : ℕ) :
    (fun i j => (mvMapGraded R (R ⧸ adicFreeTwistHomStageIdeal R a k) n).gradedAddHom d
      (adicPolynomialMatrix R a n I J d m hm i j)) = m k := by
  funext i j
  apply Subtype.ext
  exact MvPolynomial.homogeneousAdicLift_map a d (fun k => m k i j)
    (fun k => hm k i j) k

variable [Finite J]

/-- The actual native cokernel of the lifted matrix on projective space. -/
def adicPolynomialMatrixSheaf : (Proj 𝒜).Modules :=
  cokernel (polynomialMatrixHom R n I J d (adicPolynomialMatrix R a n I J d m hm))

/-- The constructed native matrix cokernel is quasicoherent. -/
theorem adicPolynomialMatrixSheaf_isQuasicoherent :
    SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf)
      (adicPolynomialMatrixSheaf R a n I J d m hm) := by
  let P : (Proj 𝒜).Modules := SheafOfModules.free I
  let Q : (Proj 𝒜).Modules := SheafOfModules.free J
  have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) P := inferInstance
  have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) Q := inferInstance
  let T : (Proj 𝒜).Modules := Q ⊗ (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) T :=
    isQuasicoherent_tensor_twistingSheaf R n Q d
  exact isQuasicoherent_cokernel (M := P) (N := T)
    (polynomialMatrixHom R n I J d (adicPolynomialMatrix R a n I J d m hm))

/-- The actual matrix cokernel has finite type, supplied by its
original epimorphic quotient of a finite free twist. -/
theorem adicPolynomialMatrixSheaf_isFiniteType :
    SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf)
      (adicPolynomialMatrixSheaf R a n I J d m hm) := by
  let Q : (Proj 𝒜).Modules := SheafOfModules.free J
  have : SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf) Q :=
    finiteType_free (X := Proj 𝒜) J
  let T : (Proj 𝒜).Modules := Q ⊗ (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf) T :=
    isFiniteType_tensor_twistingSheaf R n Q d
  exact finiteType_cokernel (N := T)
    (polynomialMatrixHom R n I J d (adicPolynomialMatrix R a n I J d m hm))

/-- Every original matrix cokernel is recovered by actual scheme
pullback from the constructed sheaf over the complete ring. -/
def adicPolynomialMatrixSheafReductionIso (k : ℕ) :
    (Scheme.Modules.pullback (map R (R ⧸ adicFreeTwistHomStageIdeal R a k) n)).obj
        (adicPolynomialMatrixSheaf R a n I J d m hm) ≅
      cokernel (polynomialMatrixHom (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d (m k)) :=
  polynomialMatrixCokernelBaseChangeIso R (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d
      (adicPolynomialMatrix R a n I J d m hm) ≪≫
    cokernelIsoOfEq (congrArg
      (polynomialMatrixHom (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d)
      (adicPolynomialMatrix_reduction R a n I J d m hm k))

/-- Stage recovery preserves the original quotient map from the
free twist; it is an isomorphism of the actual presentations. -/
theorem adicPolynomialMatrixSheafReductionIso_projection (k : ℕ) :
    (Scheme.Modules.pullback (map R (R ⧸ adicFreeTwistHomStageIdeal R a k) n)).map
        (cokernel.π (polynomialMatrixHom R n I J d
          (adicPolynomialMatrix R a n I J d m hm))) ≫
      (adicPolynomialMatrixSheafReductionIso R a n I J d m hm k).hom =
        (freeTwistBaseChangeIso R (R ⧸ adicFreeTwistHomStageIdeal R a k) n J d).hom ≫
          cokernel.π
            (polynomialMatrixHom (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d (m k)) :=
  polynomialMatrixCokernelBaseChangeIso_projection_of_eq
    R (R ⧸ adicFreeTwistHomStageIdeal R a k) n I J d
    (adicPolynomialMatrix R a n I J d m hm) (m k)
    (adicPolynomialMatrix_reduction R a n I J d m hm k)

end AlgebraicGeometry.ProjSpace
