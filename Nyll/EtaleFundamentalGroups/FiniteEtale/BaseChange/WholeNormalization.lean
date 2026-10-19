/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericFiber
import Nyll.SchemeTheory.Normalization.GenericFiber.FiniteEtaleNormalization
import Nyll.SchemeTheory.RingTheory.GenericFiber.Finite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Recovering the whole base-changed cover from its generic normalization

Let `T / R` be a finite étale extension of domains, with compatible
fraction fields `L / K`. For a normal domain `B / R` with fraction field
`F / K`, the actual base change `B ⊗[R] T` is the integral closure of `B`
in the whole generic tensor product `F ⊗[K] L`.

The generic tensor comparison is constructed from the original fraction
maps and tensor reassociation. The normalization comparison therefore
recovers every component of the original base change. Its calculation
on pure tensors preserves the two original structural maps, as required
for the overlap comparisons of normalized cover extensions.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uB uT uK uL uF

variable (R : Type uR) (B : Type uB) (T : Type uT)
  (K : Type uK) (L : Type uL) (F : Type uF)
  [CommRing R] [IsDomain R]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B]
  [CommRing T] [IsDomain T] [Algebra R T]
  [Module.Finite R T] [Algebra.Etale R T]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra R L] [Algebra T L] [Algebra K L]
  [IsScalarTower R T L] [IsScalarTower R K L] [IsFractionRing T L]
  [Field F] [Algebra R F] [Algebra B F] [Algebra K F]
  [IsScalarTower R B F] [IsScalarTower R K F] [IsFractionRing B F]

/-- The actual finite étale base change is the full normalization in the
generic tensor product, including all its generic components. -/
def finiteEtaleBaseChangeIntegralClosureEquiv :
    B ⊗[R] T ≃ₐ[B] integralClosure B (F ⊗[K] L) := by
  let U := B ⊗[R] T
  have : Module.Finite B U := Module.Finite.base_change R B T
  have : Algebra.Etale B U := Algebra.Etale.baseChange R T B
  let : Algebra F (U ⊗[B] F) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B F (U ⊗[B] F) := Algebra.TensorProduct.right_isScalarTower
  let eField : K ⊗[R] T ≃ₐ[K] L :=
    finiteGenericFiberAlgEquiv (R := R) (C := T) (K := K) (E := L)
  let eGeneric : U ⊗[B] F ≃ₐ[F] F ⊗[K] L :=
    (baseChangeGenericFiberEquiv R B T F).trans
      (iteratedGenericFiberEquiv R K F T L eField)
  exact (SchemeTheory.finiteEtaleGenericIntegralClosureEquiv B U F).trans
    (eGeneric.restrictScalars B).mapIntegralClosure

/-- The normalization comparison sends a tensor of original elements
to the corresponding tensor of their original fraction-field images. -/
theorem finiteEtaleBaseChangeIntegralClosureEquiv_tmul (b : B) (t : T) :
    (finiteEtaleBaseChangeIntegralClosureEquiv R B T K L F (b ⊗ₜ[R] t) : F ⊗[K] L) =
      algebraMap B F b ⊗ₜ[K] algebraMap T L t := by
  let U := B ⊗[R] T
  have : Module.Finite B U := Module.Finite.base_change R B T
  have : Algebra.Etale B U := Algebra.Etale.baseChange R T B
  let : Algebra F (U ⊗[B] F) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B F (U ⊗[B] F) := Algebra.TensorProduct.right_isScalarTower
  let eField : K ⊗[R] T ≃ₐ[K] L :=
    finiteGenericFiberAlgEquiv (R := R) (C := T) (K := K) (E := L)
  let eGeneric : U ⊗[B] F ≃ₐ[F] F ⊗[K] L :=
    (baseChangeGenericFiberEquiv R B T F).trans
      (iteratedGenericFiberEquiv R K F T L eField)
  change eGeneric
    (SchemeTheory.finiteEtaleGenericIntegralClosureEquiv B U F (b ⊗ₜ[R] t) : U ⊗[B] F) = _
  rw [SchemeTheory.finiteEtaleGenericIntegralClosureEquiv_val]
  change (iteratedGenericFiberEquiv R K F T L eField)
    ((baseChangeGenericFiberEquiv R B T F) ((b ⊗ₜ[R] t) ⊗ₜ[B] 1)) = _
  simp only [baseChangeGenericFiberEquiv, iteratedGenericFiberEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.commRight_symm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, eField, Algebra.smul_def, mul_one]
  change algebraMap B F b ⊗ₜ[K]
    (finiteGenericFiberAlgEquiv (R := R) (C := T) (K := K) (E := L) (1 ⊗ₜ[R] t)) = _
  rw [finiteGenericFiberAlgEquiv_tmul, map_one, one_mul]

end EtaleFundamentalGroups
