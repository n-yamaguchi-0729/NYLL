/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Adic.MappedIdeal
import Nyll.EtaleFundamentalGroups.Completions.Adic.PowerCofinality
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.CompletionAdic
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.RootCompletionBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual completion of a uniformizer root over an arbitrary DVR

Let `W = V[X] / (X ^ n - π)`, where `π` is a uniformizer of the DVR `V`.
The standard completion of `W` is canonically the same root ring formed
over the standard completion of `V`. The comparison fixes `W`, through
the original completion base-change map.

The proof computes the extended maximal ideal as the `n`-th power of the
maximal ideal of `W`. Finite free completion base change and cofinality of
these ideal powers then identify the two actual completions. No ambient
two-dimensional ring, completeness hypothesis, or comparison map is input.

This comparison is used to descend the local ramification removal in
Stacks Project, Proposition 58.30.2, https://stacks.math.columbia.edu/tag/0C0Q.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v

/-- The standard completion of the actual root DVR agrees, over that DVR,
with the root ring over the completed base. -/
def uniformizerRootStandardCompletionAlgEquiv
    (V : Type u) (K : Type v)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (n : ℕ) (hn : 0 < n) (π : V) (hπ : Prime π) :
    let W := AdjoinRoot (X ^ n - C π)
    let : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : IsDiscreteValuationRing W :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let What := standardDVFCompletionValuationSubring W (FractionRing W)
    let : Algebra W What :=
      standardDVFCompletionValuationSubringAlgebra W (FractionRing W)
    let Vhat := standardDVFCompletionValuationSubring V K
    let : Algebra V Vhat := standardDVFCompletionValuationSubringAlgebra V K
    let Rhat := AdjoinRoot
      (X ^ n - C (standardDVRCompletionValuationSubringElement V K π))
    let : Algebra W Rhat := standardDVRRootCompletionAlgebra V K n π
    What ≃ₐ[W] Rhat := by
  intro W hDomainW hDvrW What aWWhat Vhat aVVhat Rhat aWRhat
  let I := IsLocalRing.maximalIdeal V
  let J := IsLocalRing.maximalIdeal W
  let r : W := AdjoinRoot.root (X ^ n - C π)
  have hr : Prime r := prime_adjoinRoot_root_of_prime hn hπ
  have hmap : I.map (algebraMap V W) = J ^ n := by
    change (IsLocalRing.maximalIdeal V).map (algebraMap V W) =
      IsLocalRing.maximalIdeal W ^ n
    rw [hπ.irreducible.maximalIdeal_eq, hr.irreducible.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
      AdjoinRoot.algebraMap_eq, ← adjoinRoot_root_pow]
  have : Module.Finite V W := (monic_X_pow_sub_C π hn.ne').finite_adjoinRoot
  have : Module.Free V W := (monic_X_pow_sub_C π hn.ne').free_adjoinRoot
  let eBase : AdicCompletion I V ≃ₐ[V] Vhat :=
    standardDVRAdicCompletionEquivCompletionValuationSubring V K
  let T := Vhat ⊗[V] W
  let T₀ := AdicCompletion I V ⊗[V] W
  let : Algebra W T := Algebra.TensorProduct.rightAlgebra
  let : Algebra W T₀ := Algebra.TensorProduct.rightAlgebra
  let eTensor₀ : T ≃ₐ[V] T₀ :=
    Algebra.TensorProduct.congr eBase.symm (AlgEquiv.refl : W ≃ₐ[V] W)
  let eTensor : T ≃ₐ[W] T₀ :=
    AlgEquiv.ofRingEquiv (R := W) (f := eTensor₀.toRingEquiv) (fun w ↦ by
      change (Algebra.TensorProduct.congr eBase.symm
        (AlgEquiv.refl : W ≃ₐ[V] W)) (1 ⊗ₜ[V] w) = 1 ⊗ₜ[V] w
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      simp only [map_one, AlgEquiv.refl_toAlgHom, AlgHom.id_apply])
  let eMapped₀ : T₀ ≃+* AdicCompletion (I.map (algebraMap V W)) W :=
    tensorProductMappedIdealCompletionFreeRingEquiv I
  let eMapped : T₀ ≃ₐ[W] AdicCompletion (I.map (algebraMap V W)) W :=
    AlgEquiv.ofRingEquiv (R := W) (f := eMapped₀) (fun w ↦ by
      change eMapped₀ (Algebra.TensorProduct.includeRight w) =
        AdicCompletion.of (I.map (algebraMap V W)) W w
      exact tensorProductMappedIdealCompletionFreeRingEquiv_includeRight_apply I w)
  let ePower : AdicCompletion (I.map (algebraMap V W)) W ≃ₐ[W]
      AdicCompletion J W := by
    rw [hmap]
    exact adicCompletionPowerAlgEquiv J n hn
  let eActual : AdicCompletion J W ≃ₐ[W] What :=
    standardDVRAdicCompletionEquivCompletionValuationSubring W (FractionRing W)
  let eCompletion : T ≃ₐ[W] Rhat :=
    standardDVRRootCompletionAlgEquivOverRoot V K n π
  exact (((eActual.symm.trans ePower.symm).trans eMapped.symm).trans
    eTensor.symm).trans eCompletion

end EtaleFundamentalGroups.Kummer
