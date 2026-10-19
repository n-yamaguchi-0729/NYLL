/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.GenericFiber.SmoothIntegralClosure
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Recovering finite étale algebras from their generic fibres

A finite étale algebra over a normal domain is the literal integral
closure of the base in its entire generic fibre. The comparison sends an
element to its original pure tensor and includes every generic component.

Consequently every isomorphism of the generic fibres extends to an
isomorphism of the original finite étale algebras. The extension preserves
the specified generic isomorphism. This supplies the affine overlap
comparison used when finite étale extensions of a generic cover are glued.
-/

noncomputable section

open scoped TensorProduct

namespace SchemeTheory

universe uR uT uU uK

/-- The original generic-fibre inclusion takes a finite algebra into the
integral closure of the base in the whole generic fibre. -/
def finiteAlgebraToGenericIntegralClosure
    (R : Type uR) (T : Type uT) (K : Type uK)
    [CommRing R] [CommRing T] [Algebra R T] [Module.Finite R T]
    [CommRing K] [Algebra R K] :
    T →ₐ[R] integralClosure R (T ⊗[R] K) := by
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  let i : T →ₐ[R] T ⊗[R] K := Algebra.TensorProduct.includeLeft
  exact i.codRestrict _ fun t ↦ (Algebra.IsIntegral.isIntegral (R := R) t).map i

/-- Over a normal domain, finite étaleness makes the original inclusion
onto the full integral closure of the base in the generic fibre. -/
theorem finiteAlgebraToGenericIntegralClosure_bijective
    (R : Type uR) (T : Type uT) (K : Type uK)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Bijective (finiteAlgebraToGenericIntegralClosure R T K) := by
  have hi : Function.Injective (Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] K) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R K)
  constructor
  · intro t₁ t₂ h
    exact hi (congrArg (fun z : integralClosure R (T ⊗[R] K) ↦ (z : T ⊗[R] K)) h)
  · intro z
    obtain ⟨t, ht⟩ :=
      EtaleFundamentalGroups.exists_eq_includeLeft_of_isIntegral_genericFiber_of_smooth
        (R := R) (S := T) (K := K) (z : T ⊗[R] K) z.property.tower_top
    exact ⟨t, Subtype.ext ht⟩

/-- A finite étale algebra over a normal domain is its full generic
integral closure through the original generic-fibre inclusion. -/
def finiteEtaleGenericIntegralClosureEquiv
    (R : Type uR) (T : Type uT) (K : Type uK)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    T ≃ₐ[R] integralClosure R (T ⊗[R] K) :=
  AlgEquiv.ofBijective (finiteAlgebraToGenericIntegralClosure R T K)
    (finiteAlgebraToGenericIntegralClosure_bijective R T K)

/-- The normalization comparison retains the actual generic tensor of
each original element. -/
theorem finiteEtaleGenericIntegralClosureEquiv_val
    (R : Type uR) (T : Type uT) (K : Type uK)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K] (t : T) :
    (finiteEtaleGenericIntegralClosureEquiv R T K t : T ⊗[R] K) = t ⊗ₜ[R] 1 := rfl

/-- An isomorphism of the entire generic fibres extends to the original
finite étale algebras over the normal base. -/
def finiteEtaleEquivOfGenericEquiv
    (R : Type uR) (T : Type uT) (U : Type uU) (K : Type uK)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [CommRing U] [Algebra R U] [Module.Finite R U] [Algebra.Etale R U]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    let : Algebra K (T ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
    let : Algebra K (U ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
    (T ⊗[R] K ≃ₐ[K] U ⊗[R] K) → (T ≃ₐ[R] U) := by
  intro aKT aKU e
  have : IsScalarTower R K (T ⊗[R] K) := Algebra.TensorProduct.right_isScalarTower
  have : IsScalarTower R K (U ⊗[R] K) := Algebra.TensorProduct.right_isScalarTower
  exact (finiteEtaleGenericIntegralClosureEquiv R T K).trans
    ((e.restrictScalars R).mapIntegralClosure.trans
      (finiteEtaleGenericIntegralClosureEquiv R U K).symm)

/-- The extended isomorphism has exactly the prescribed value on every
original generic tensor. -/
theorem finiteEtaleEquivOfGenericEquiv_tmul_one
    (R : Type uR) (T : Type uT) (U : Type uU) (K : Type uK)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [CommRing U] [Algebra R U] [Module.Finite R U] [Algebra.Etale R U]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    let : Algebra K (T ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
    let : Algebra K (U ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
    ∀ (e : T ⊗[R] K ≃ₐ[K] U ⊗[R] K) (t : T),
      finiteEtaleEquivOfGenericEquiv R T U K e t ⊗ₜ[R] (1 : K) = e (t ⊗ₜ[R] 1) := by
  intro aKT aKU e t
  have : IsScalarTower R K (T ⊗[R] K) := Algebra.TensorProduct.right_isScalarTower
  have : IsScalarTower R K (U ⊗[R] K) := Algebra.TensorProduct.right_isScalarTower
  let eT := finiteEtaleGenericIntegralClosureEquiv R T K
  let eU := finiteEtaleGenericIntegralClosureEquiv R U K
  let eI := (e.restrictScalars R).mapIntegralClosure
  change eU.symm (eI (eT t)) ⊗ₜ[R] (1 : K) = e (t ⊗ₜ[R] 1)
  calc
    _ = (eU (eU.symm (eI (eT t))) : U ⊗[R] K) :=
      (finiteEtaleGenericIntegralClosureEquiv_val R U K _).symm
    _ = (eI (eT t) : U ⊗[R] K) :=
      congrArg (fun z : integralClosure R (U ⊗[R] K) ↦ (z : U ⊗[R] K))
        (eU.apply_symm_apply _)
    _ = _ := rfl

end SchemeTheory
