/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationCompletion
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Actual formal-fiber comparison before splitting the henselization fiber

The completion isomorphism preserving the original local-ring map is
an isomorphism of original-base algebras. Tensor base change then compares
the original formal fiber with completion tensored over the henselization
against its actual original-prime fiber. The formula retains every pure
tensor, including the original residue-field coordinate.

This is the unsplit tensor comparison in the henselization argument for
G-rings. It asserts no geometric regularity or smooth factorization.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The original formal fiber is the completion base change of the
actual henselization fiber, with both tensor coordinates retained. -/
theorem ordinaryHenselization_exists_formalFiberComparison
    (R : Type u) [CommRing R] [IsLocalRing R] (p : Ideal R) [p.IsPrime] :
    let H := ordinaryHenselization R
    let : Algebra R H := (ordinaryHenselizationMap R).toAlgebra
    let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let Hhat := AdicCompletion (IsLocalRing.maximalIdeal H) H
    let : IsScalarTower R H Hhat := IsScalarTower.of_algebraMap_eq' rfl
    ∃ (E : Rhat ≃ₐ[R] Hhat)
      (F : (Rhat ⊗[R] p.ResidueField) ≃ₐ[R]
        (Hhat ⊗[H] (H ⊗[R] p.ResidueField))),
      ∀ (x : Rhat) (a : p.ResidueField),
        F (x ⊗ₜ[R] a) = E x ⊗ₜ[H] ((1 : H) ⊗ₜ[R] a) := by
  intro H actualStructureAlgebra Rhat Hhat actualCompletionTower
  obtain ⟨e, he⟩ := ordinaryHenselization_exists_completionEquiv R
  let E : Rhat ≃ₐ[R] Hhat :=
    { __ := e
      commutes' r := (he r).trans (IsScalarTower.algebraMap_apply R H Hhat r).symm }
  let c : Hhat ⊗[H] (H ⊗[R] p.ResidueField) ≃ₐ[R] Hhat ⊗[R] p.ResidueField :=
    (Algebra.TensorProduct.cancelBaseChange R H H Hhat p.ResidueField).restrictScalars R
  let F : (Rhat ⊗[R] p.ResidueField) ≃ₐ[R]
      (Hhat ⊗[H] (H ⊗[R] p.ResidueField)) :=
    (Algebra.TensorProduct.congr E (AlgEquiv.refl : p.ResidueField ≃ₐ[R] p.ResidueField)).trans
      c.symm
  refine ⟨E, F, ?_⟩
  intro x a
  change c.symm (E x ⊗ₜ[R] a) = E x ⊗ₜ[H] ((1 : H) ⊗ₜ[R] a)
  exact Algebra.TensorProduct.cancelBaseChange_symm_tmul R H H Hhat p.ResidueField (E x) a

end EtaleFundamentalGroups.StrictHenselian
