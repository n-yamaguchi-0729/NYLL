/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeQuotient
import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentCokernel
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.AdicFreeTwistHom
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.PolynomialHomPullback
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Algebraization of cokernels of compatible native presenting morphisms

The input consists of original native free-to-finite-free-twist
morphisms, compatible under their actual scheme pullbacks. The
constructed native lift gives a quasicoherent finite-type cokernel
over the complete ring. Its pullback to each adic quotient is the
cokernel of the original stage morphism, and the comparison retains
the actual quotient projections.

Neither compatible polynomial entries nor a lifted sheaf or stage
comparison is supplied as extra data. Constructing a uniformly sized
compatible presentation of an arbitrary formal coherent sheaf remains
a separate geometric step.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

private theorem cokernelComparison_comp_eq
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasCokernels C]
    {P L M N : C} (f g : M ⟶ N) (h : f = g)
    (p : P ⟶ L) (e : L ≅ cokernel f) (q : P ⟶ N)
    (hp : p ≫ e.hom = q ≫ cokernel.π f) :
    p ≫ (e ≪≫ cokernelIsoOfEq h).hom = q ≫ cokernel.π g := by
  change p ≫ (e.hom ≫ (cokernelIsoOfEq h).hom) = _
  rw [← Category.assoc, hp, Category.assoc, π_comp_cokernelIsoOfEq_hom]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (n : ℕ) (I J : Type u) [Finite J] (d : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

private theorem freeTwistHomPullback_square (φ : FreeTwistHom R n I J d) :
    (Scheme.Modules.pullback (map R A n)).map φ ≫
        (freeTwistBaseChangeIso R A n J d).hom =
      (pullbackFreeIso (map R A n) I).hom ≫
        freeTwistHomPullback R A (algebraMap R A) n I J d φ := by
  let P : (Proj 𝒜R).Modules := SheafOfModules.free I
  let Q : (Proj 𝒜A).Modules := SheafOfModules.free I
  let T : (Proj 𝒜A).Modules :=
    (show (Proj 𝒜A).Modules from SheafOfModules.free J) ⊗
      (twistingSheaf A n).tensorPow d
  let p : (Scheme.Modules.pullback (map R A n)).obj P ≅ Q :=
    pullbackFreeIso (map R A n) I
  let v : (Scheme.Modules.pullback (map R A n)).obj P ⟶ T :=
    (Scheme.Modules.pullback (map R A n)).map φ ≫
      (freeTwistBaseChangeIso R A n J d).hom
  have he : v = p.hom ≫ (p.inv ≫ v) := (p.hom_inv_id_assoc v).symm
  dsimp only [freeTwistHomPullback]
  rw [toAlgebra_algebraMap]
  exact he

/-- Actual pullback carries the cokernel of a native presenting
morphism to the cokernel of its actual transported morphism. -/
def freeTwistHomCokernelBaseChangeIso (φ : FreeTwistHom R n I J d) :
    (Scheme.Modules.pullback (map R A n)).obj (cokernel φ) ≅
      cokernel (freeTwistHomPullback R A (algebraMap R A) n I J d φ) :=
  PreservesCokernel.iso (Scheme.Modules.pullback (map R A n)) φ ≪≫
    cokernel.mapIso ((Scheme.Modules.pullback (map R A n)).map φ)
      (freeTwistHomPullback R A (algebraMap R A) n I J d φ)
      (pullbackFreeIso (map R A n) I) (freeTwistBaseChangeIso R A n J d)
      (freeTwistHomPullback_square R A n I J d φ)

/-- The comparison is compatible with the original native cokernel
projection from the pulled-back free twist. -/
theorem freeTwistHomCokernelBaseChangeIso_projection (φ : FreeTwistHom R n I J d) :
    (Scheme.Modules.pullback (map R A n)).map (cokernel.π φ) ≫
        (freeTwistHomCokernelBaseChangeIso R A n I J d φ).hom =
      (freeTwistBaseChangeIso R A n J d).hom ≫
        cokernel.π (freeTwistHomPullback R A (algebraMap R A) n I J d φ) := by
  change (Scheme.Modules.pullback (map R A n)).map (cokernel.π φ) ≫
    ((PreservesCokernel.iso (Scheme.Modules.pullback (map R A n)) φ).hom ≫
      (cokernel.mapIso ((Scheme.Modules.pullback (map R A n)).map φ)
        (freeTwistHomPullback R A (algebraMap R A) n I J d φ)
        (pullbackFreeIso (map R A n) I) (freeTwistBaseChangeIso R A n J d)
        (freeTwistHomPullback_square R A n I J d φ)).hom) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

omit A [CommRing A] [Algebra R A] [Finite J] in
private theorem freeTwistCokernel_quasicoherent (φ : FreeTwistHom R n I J d) :
    SheafOfModules.IsQuasicoherent (R := (Proj 𝒜R).ringCatSheaf) (cokernel φ) := by
  let P : (Proj 𝒜R).Modules := SheafOfModules.free I
  let Q : (Proj 𝒜R).Modules := SheafOfModules.free J
  have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜R).ringCatSheaf) P := inferInstance
  have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜R).ringCatSheaf) Q := inferInstance
  let T : (Proj 𝒜R).Modules := Q ⊗ (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsQuasicoherent (R := (Proj 𝒜R).ringCatSheaf) T :=
    isQuasicoherent_tensor_twistingSheaf R n Q d
  exact isQuasicoherent_cokernel (M := P) (N := T) φ

private theorem finiteType_free {X : Scheme.{u}} (K : Type u) [Finite K] :
    (SheafOfModules.free (R := X.ringCatSheaf) K).IsFiniteType := by
  let g := SheafOfModules.free.generatingSections (R := X.ringCatSheaf) K
  let q := g.localGeneratorsData
  have hq : q.IsFiniteType := by
    constructor
    intro U
    exact ⟨inferInstanceAs (Finite K)⟩
  exact q.isFiniteType hq

private theorem finiteType_cokernel {X : Scheme.{u}} {M N : X.Modules}
    [SheafOfModules.IsFiniteType (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf) (cokernel φ) := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  have : (E.functor.obj N).IsFiniteType :=
    inferInstanceAs (SheafOfModules.IsFiniteType (R := X.ringCatSheaf) N)
  exact SheafOfModules.isFiniteType_of_epi
    (C := X.Opens) (R := X.ringCatSheaf)
    (M := E.functor.obj N) (N := E.functor.obj (cokernel φ))
    (E.functor.map (cokernel.π φ))

omit A [CommRing A] [Algebra R A] in
private theorem freeTwistCokernel_finiteType (φ : FreeTwistHom R n I J d) :
    SheafOfModules.IsFiniteType (R := (Proj 𝒜R).ringCatSheaf) (cokernel φ) := by
  let Q : (Proj 𝒜R).Modules := SheafOfModules.free J
  have : SheafOfModules.IsFiniteType (R := (Proj 𝒜R).ringCatSheaf) Q :=
    finiteType_free (X := Proj 𝒜R) J
  let T : (Proj 𝒜R).Modules := Q ⊗ (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsFiniteType (R := (Proj 𝒜R).ringCatSheaf) T :=
    isFiniteType_tensor_twistingSheaf R n Q d
  exact finiteType_cokernel (N := T) φ

omit A [CommRing A] [Algebra R A]

variable (a : Ideal R) [IsAdicComplete a R]
  (φ : adicFreeTwistHomSections R a n I J d)

/-- The actual native cokernel of the uniquely reconstructed
presenting morphism over the complete coefficient ring. -/
def adicFreeTwistCokernel : (Proj 𝒜R).Modules :=
  cokernel (adicFreeTwistHomLift R a n I J d φ)

/-- The reconstructed native cokernel is quasicoherent. -/
theorem adicFreeTwistCokernel_isQuasicoherent :
    SheafOfModules.IsQuasicoherent (R := (Proj 𝒜R).ringCatSheaf)
      (adicFreeTwistCokernel R n I J d a φ) :=
  freeTwistCokernel_quasicoherent R n I J d (adicFreeTwistHomLift R a n I J d φ)

/-- The original finite free target supplies finite type of the
reconstructed native cokernel. -/
theorem adicFreeTwistCokernel_isFiniteType :
    SheafOfModules.IsFiniteType (R := (Proj 𝒜R).ringCatSheaf)
      (adicFreeTwistCokernel R n I J d a φ) :=
  freeTwistCokernel_finiteType R n I J d (adicFreeTwistHomLift R a n I J d φ)

/-- Original stage cokernels are recovered under actual coefficient
pullback, using the proved reduction of the native presenting morphism. -/
def adicFreeTwistCokernelReductionIso (k : ℕ) :
    (Scheme.Modules.pullback (map R (R ⧸ a ^ (k + 1)) n)).obj
        (adicFreeTwistCokernel R n I J d a φ) ≅ cokernel (φ.val k) :=
  freeTwistHomCokernelBaseChangeIso R (R ⧸ a ^ (k + 1)) n I J d
      (adicFreeTwistHomLift R a n I J d φ) ≪≫
    cokernelIsoOfEq (adicFreeTwistHomLift_reduction R a n I J d φ k)

/-- Recovery preserves the original quotient map at every stage. -/
theorem adicFreeTwistCokernelReductionIso_projection (k : ℕ) :
    (Scheme.Modules.pullback (map R (R ⧸ a ^ (k + 1)) n)).map
        (cokernel.π (adicFreeTwistHomLift R a n I J d φ)) ≫
      (adicFreeTwistCokernelReductionIso R n I J d a φ k).hom =
        (freeTwistBaseChangeIso R (R ⧸ a ^ (k + 1)) n J d).hom ≫ cokernel.π (φ.val k) := by
  let ψ : FreeTwistHom R n I J d := adicFreeTwistHomLift R a n I J d φ
  let ψk : FreeTwistHom (R ⧸ a ^ (k + 1)) n I J d :=
    freeTwistHomPullback R (R ⧸ a ^ (k + 1))
      (algebraMap R (R ⧸ a ^ (k + 1))) n I J d ψ
  have hk : ψk = φ.val k := adicFreeTwistHomLift_reduction R a n I J d φ k
  have hbase := freeTwistHomCokernelBaseChangeIso_projection
    R (R ⧸ a ^ (k + 1)) n I J d ψ
  exact cokernelComparison_comp_eq ψk (φ.val k) hk _
    (freeTwistHomCokernelBaseChangeIso R (R ⧸ a ^ (k + 1)) n I J d ψ) _ hbase

end AlgebraicGeometry.ProjSpace
