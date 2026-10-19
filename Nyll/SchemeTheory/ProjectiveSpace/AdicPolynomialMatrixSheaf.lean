/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeQuotient
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentCokernel
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
import Nyll.SchemeTheory.ProjectiveSpace.PolynomialMatrixCokernel
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Nyll.SchemeTheory.RingTheory.AdicCompletion.HomogeneousPolynomialSystem
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.MvPolynomial.Homogeneous

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

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

private theorem finiteType_free {X : Scheme.{u}} (J : Type u) [Finite J] :
    (SheafOfModules.free (R := X.ringCatSheaf) J).IsFiniteType := by
  let g := SheafOfModules.free.generatingSections (R := X.ringCatSheaf) J
  let q : (SheafOfModules.free (R := X.ringCatSheaf) J).LocalGeneratorsData :=
    g.localGeneratorsData
  have hq : q.IsFiniteType := by
    constructor
    intro U
    refine { finite := ?_ }
    exact (show Finite J from inferInstance)
  exact q.isFiniteType hq

private theorem finiteType_cokernel {X : Scheme.{u}} {M N : X.Modules}
    [SheafOfModules.IsFiniteType (R := X.ringCatSheaf) N] (f : M ⟶ N) :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf) (cokernel f) := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  have : (E.functor.obj N).IsFiniteType :=
    inferInstanceAs (SheafOfModules.IsFiniteType (R := X.ringCatSheaf) N)
  exact SheafOfModules.isFiniteType_of_epi
    (C := X.Opens) (R := X.ringCatSheaf)
    (M := E.functor.obj N) (N := E.functor.obj (cokernel f))
    (E.functor.map (cokernel.π f))

private theorem cokernelComparison_comp_eq
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasCokernels C]
    {P L M N : C} (f g : M ⟶ N) (h : f = g)
    (p : P ⟶ L) (e : L ≅ cokernel f) (q : P ⟶ N)
    (hp : p ≫ e.hom = q ≫ cokernel.π f) :
    p ≫ (e ≪≫ cokernelIsoOfEq h).hom = q ≫ cokernel.π g := by
  change p ≫ (e.hom ≫ (cokernelIsoOfEq h).hom) = _
  rw [← Category.assoc, hp, Category.assoc, π_comp_cokernelIsoOfEq_hom]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (a : Ideal R) [IsAdicComplete a R]
  (n : ℕ) (I J : Type u) (d : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
variable (m : (k : ℕ) → I → J →
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (R ⧸ a ^ (k + 1)) d)
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
    (fun i j => (mvMapGraded R (R ⧸ a ^ (k + 1)) n).gradedAddHom d
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
    (Scheme.Modules.pullback (map R (R ⧸ a ^ (k + 1)) n)).obj
        (adicPolynomialMatrixSheaf R a n I J d m hm) ≅
      cokernel (polynomialMatrixHom (R ⧸ a ^ (k + 1)) n I J d (m k)) :=
  polynomialMatrixCokernelBaseChangeIso R (R ⧸ a ^ (k + 1)) n I J d
      (adicPolynomialMatrix R a n I J d m hm) ≪≫
    cokernelIsoOfEq (congrArg (polynomialMatrixHom (R ⧸ a ^ (k + 1)) n I J d)
      (adicPolynomialMatrix_reduction R a n I J d m hm k))

/-- Stage recovery preserves the original quotient map from the
free twist; it is an isomorphism of the actual presentations. -/
theorem adicPolynomialMatrixSheafReductionIso_projection (k : ℕ) :
    (Scheme.Modules.pullback (map R (R ⧸ a ^ (k + 1)) n)).map
        (cokernel.π (polynomialMatrixHom R n I J d
          (adicPolynomialMatrix R a n I J d m hm))) ≫
      (adicPolynomialMatrixSheafReductionIso R a n I J d m hm k).hom =
        (freeTwistBaseChangeIso R (R ⧸ a ^ (k + 1)) n J d).hom ≫
          cokernel.π (polynomialMatrixHom (R ⧸ a ^ (k + 1)) n I J d (m k)) := by
  let mR : I → J → 𝒜 d := adicPolynomialMatrix R a n I J d m hm
  let mA : I → J →
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (R ⧸ a ^ (k + 1)) d :=
    fun i j => (mvMapGraded R (R ⧸ a ^ (k + 1)) n).gradedAddHom d (mR i j)
  have hmatrix : mA = m k := adicPolynomialMatrix_reduction R a n I J d m hm k
  have hbase := polynomialMatrixCokernelBaseChangeIso_projection
    R (R ⧸ a ^ (k + 1)) n I J d mR
  exact cokernelComparison_comp_eq
    (polynomialMatrixHom (R ⧸ a ^ (k + 1)) n I J d mA)
    (polynomialMatrixHom (R ⧸ a ^ (k + 1)) n I J d (m k))
    (congrArg (polynomialMatrixHom (R ⧸ a ^ (k + 1)) n I J d) hmatrix)
    _ (polynomialMatrixCokernelBaseChangeIso R (R ⧸ a ^ (k + 1)) n I J d mR) _ hbase

end AlgebraicGeometry.ProjSpace
