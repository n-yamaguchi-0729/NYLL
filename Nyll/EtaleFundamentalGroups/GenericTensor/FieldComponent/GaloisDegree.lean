/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Divisibility of Galois tensor-component degrees

After arbitrary field extension, the degree of each field component of a
finite Galois extension divides the original degree. Restriction embeds its
Galois group into the original Galois group: an automorphism fixing both
tensor factors fixes the actual quotient, since the quotient map is
surjective. Lagrange's theorem then gives divisibility.

In particular a prime-to-p Galois degree remains prime to p on every
component after completion. Unlike a numerical upper bound, this permits
the original degree itself to be a common tame root exponent.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uK uF uL

/-- Every literal tensor-field component of a finite Galois extension has
degree dividing the original Galois degree. -/
theorem genericTensorFieldComponent_finrank_dvd_of_isGalois
    {K : Type uK} {F : Type uF} {L : Type uL}
    [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    Module.finrank F (GenericTensorFieldComponent m) ∣ Module.finrank K L := by
  let P := GenericTensorFieldComponent m
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  have : IsScalarTower K L P := genericTensorFieldComponent_right_isScalarTower m
  have : IsScalarTower K F P := genericTensorFieldComponent_isScalarTower m
  let rho : Gal(P/F) →* Gal(L/K) :=
    IntermediateField.restrictRestrictAlgEquivMapHom K L F P
  have hInjective : Function.Injective rho := by
    refine (injective_iff_map_eq_one rho).mpr ?_
    intro sigma hSigma
    have hRight (b : L) : sigma (genericTensorFieldComponentRight m b) =
        genericTensorFieldComponentRight m b := by
      have h := AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgAut Gal(P/F) K P sigma) L b
      change algebraMap L P ((rho sigma) b) = sigma (algebraMap L P b) at h
      rw [hSigma] at h
      exact h.symm
    have hTensor (a : F) (b : L) :
        (Ideal.Quotient.mk m (a ⊗ₜ[K] b) : P) =
          algebraMap F P a * genericTensorFieldComponentRight m b := by
      simpa only [Algebra.TensorProduct.productMap_apply_tmul,
        genericTensorFieldComponentLeft_eq_algebraMap, Ideal.Quotient.mkₐ_eq_mk] using
        (DFunLike.congr_fun (genericTensorFieldComponent_productMap_eq_quotient m)
          (a ⊗ₜ[K] b)).symm
    apply AlgEquiv.ext
    intro x
    change sigma x = x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a b
      rw [hTensor, map_mul, sigma.commutes, hRight]
    · intro a b ha hb
      simpa only [map_add] using congrArg₂ (· + ·) ha hb
  have hCard : Nat.card Gal(P/F) ∣ Nat.card Gal(L/K) :=
    Subgroup.card_dvd_of_injective rho hInjective
  simpa only [IsGalois.card_aut_eq_finrank] using hCard

end EtaleFundamentalGroups
