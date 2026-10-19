/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.Completion
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.CompletionAdic
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.ComponentPrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.RootCompletionBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The fraction-field tower for a completed uniformizer root

There are two actual maps from the original fraction field to the fraction
field of the completed root ring: first complete and then adjoin the root,
or first adjoin the root and then use the completed root-ring map. They agree
by the coefficient square in the tensor-product base-change equivalence and
the uniqueness of fraction-field extension.

This characteristic-free comparison is shared by the characteristic-zero
and tame normalization descent arguments.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct

universe uV

/-- The canonical maps through the original root fraction field and the
completed base fraction field give the same tower into the completed root
fraction field. Every map is the actual completion or fraction-ring lift. -/
theorem uniformizerRootCompletionFractionField_isScalarTower
    (V : Type uV) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (n : ℕ) (hn : 0 < n) (π : V) (hπ : Prime π) :
    let W := AdjoinRoot (X ^ n - C π)
    let : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : Module.FaithfullyFlat V W := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
    let K := FractionRing V
    let Kroot := FractionRing W
    let : Algebra K Kroot := FractionRing.liftAlgebra V Kroot
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    let : Algebra K Khat := standardDVFCompletionAlgebra V K
    let πhat : Vhat := standardDVRCompletionValuationSubringElement V K π
    let hπhat := standardDVRCompletionValuationSubringElement_isUniformizer
      V K π hπ.irreducible.maximalIdeal_eq
    let Rhat := AdjoinRoot (X ^ n - C πhat)
    let : IsDomain Rhat := completeDVFRootRing_isDomain H πhat hπhat n hn
    let Fhat := FractionRing Rhat
    let : Algebra Khat Fhat := completeDVFRootFractionFieldAlgebra H πhat hπhat n hn
    let : Algebra K Fhat := ((algebraMap Khat Fhat).comp (algebraMap K Khat)).toAlgebra
    let : Algebra W Rhat := standardDVRRootCompletionAlgebra V K n π
    let : Module.FaithfullyFlat W Rhat := standardDVRRootCompletion_faithfullyFlat V K n π
    let : FaithfulSMul W Fhat := FaithfulSMul.trans W Rhat Fhat
    let : Algebra Kroot Fhat := FractionRing.liftAlgebra W Fhat
    IsScalarTower K Kroot Fhat := by
  intro W hDomainW hFlatW K Kroot aKKroot H Vhat Khat aKKhat πhat hπhat
    Rhat hDomainRhat Fhat aKhatFhat aKFhat aWRhat hFlatWRhat hFaithful aKrootFhat
  let : Algebra V Vhat := standardDVFCompletionValuationSubringAlgebra V K
  let aVKhat : Algebra V Khat := standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat := aKKhat.toSMul
  let : SMul V Khat := aVKhat.toSMul
  have : IsScalarTower V K Khat := standardDVFCompletion_isScalarTower (V := V) (K := K)
  have : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower (V := V) (K := K)
  have : IsScalarTower Vhat Khat Fhat :=
    completeDVFRootFractionField_isScalarTower H πhat hπhat n hn
  have : IsScalarTower V K Kroot := FractionRing.isScalarTower_liftAlgebra V Kroot
  have : IsScalarTower W Kroot Fhat := FractionRing.isScalarTower_liftAlgebra W Fhat
  apply IsScalarTower.of_algebraMap_eq
  intro x
  have hMaps : algebraMap K Fhat =
      (algebraMap Kroot Fhat).comp (algebraMap K Kroot) := by
    apply IsFractionRing.ringHom_ext (A := V)
    intro v
    have hLeft :
        algebraMap Khat Fhat (algebraMap K Khat (algebraMap V K v)) =
          algebraMap Rhat Fhat (algebraMap Vhat Rhat (algebraMap V Vhat v)) := by
      calc
        _ = algebraMap Khat Fhat (algebraMap V Khat v) :=
          congrArg (algebraMap Khat Fhat) (IsScalarTower.algebraMap_apply V K Khat v).symm
        _ = algebraMap Khat Fhat (algebraMap Vhat Khat (algebraMap V Vhat v)) :=
          congrArg (algebraMap Khat Fhat) (IsScalarTower.algebraMap_apply V Vhat Khat v)
        _ = algebraMap Vhat Fhat (algebraMap V Vhat v) :=
          (IsScalarTower.algebraMap_apply Vhat Khat Fhat _).symm
        _ = algebraMap Rhat Fhat (algebraMap Vhat Rhat (algebraMap V Vhat v)) :=
          IsScalarTower.algebraMap_apply Vhat Rhat Fhat _
    have hRight :
        algebraMap Kroot Fhat (algebraMap K Kroot (algebraMap V K v)) =
          algebraMap Rhat Fhat (algebraMap W Rhat (algebraMap V W v)) := by
      calc
        _ = algebraMap Kroot Fhat (algebraMap V Kroot v) :=
          congrArg (algebraMap Kroot Fhat) (IsScalarTower.algebraMap_apply V K Kroot v).symm
        _ = algebraMap Kroot Fhat (algebraMap W Kroot (algebraMap V W v)) :=
          congrArg (algebraMap Kroot Fhat) (IsScalarTower.algebraMap_apply V W Kroot v)
        _ = algebraMap W Fhat (algebraMap V W v) :=
          (IsScalarTower.algebraMap_apply W Kroot Fhat _).symm
        _ = algebraMap Rhat Fhat (algebraMap W Rhat (algebraMap V W v)) :=
          IsScalarTower.algebraMap_apply W Rhat Fhat _
    let T := Vhat ⊗[V] W
    let iLeft : Vhat →ₐ[V] T := Algebra.TensorProduct.includeLeft
    let iRight : W →ₐ[V] T := Algebra.TensorProduct.includeRight
    let eCompletion : T ≃ₐ[Vhat] Rhat := standardDVRRootCompletionAlgEquiv V K n π
    have hVRhat : algebraMap Vhat Rhat (algebraMap V Vhat v) =
        algebraMap W Rhat (algebraMap V W v) := by
      calc
        _ = eCompletion (iLeft (algebraMap V Vhat v)) := (eCompletion.commutes _).symm
        _ = eCompletion (iRight (algebraMap V W v)) :=
          congrArg eCompletion ((iLeft.commutes v).trans (iRight.commutes v).symm)
        _ = algebraMap W Rhat (algebraMap V W v) := rfl
    exact hLeft.trans ((congrArg (algebraMap Rhat Fhat) hVRhat).trans hRight.symm)
  exact DFunLike.congr_fun hMaps x

end EtaleFundamentalGroups.Kummer
