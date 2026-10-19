/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.GaloisDegree
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Tower
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.ComponentPrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.Completions.RootTensor.PrimeToDegree
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.ComponentExtraction
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.FixedTensor.IntrinsicCoordinates
import Nyll.EtaleFundamentalGroups.Kummer.PureRadical.GenericTensorComponent
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# A common prime-to-p exponent through a completed tensor tower

Let a finite Galois extension of the original field have degree prime to
the residue characteristic of a complete valued overfield. Its actual
tensor components over that complete field still have degrees dividing
the original degree. A single root exponent divisible by that degree
therefore removes the ramification in all of them.

The final component is kept fixed throughout: contraction constructs its
intermediate component and the second quotient, whose integral closure is
canonically identified with the normalization of the original quotient.
This is the completed tensor-tower step used in Stacks Project 58.30.3:
https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct
open ValuationTheory.DiscreteValuationField

universe uK₀ uK uV uL

/-- A prime-to-p Galois degree supplies a common root exponent for every
literal component after first passing to a complete valued overfield. -/
theorem integralClosure_completeDVFRootTensorComponent_etale_of_galois_degree_coprime
    {K₀ : Type uK₀} {K : Type uK} {L : Type uL}
    [Field K₀] [Field K] [Field L] [Algebra K₀ K] [Algebra K₀ L]
    [FiniteDimensional K₀ L] [IsGalois K₀ L]
    (base : CompleteDVF.{uK, uV} K)
    (p : ℕ) (hp : p.Prime) [CharP base.residueField p]
    (hdegree : Nat.Coprime (Module.finrank K₀ L) p)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) (hdiv : Module.finrank K₀ L ∣ N) :
    let V := base.valuationSubring
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let : IsDomain Rn := completeDVFRootRing_isDomain base varpi hvarpi N hN
    let F := FractionRing Rn
    let : Algebra K F := completeDVFRootFractionFieldAlgebra base varpi hvarpi N hN
    let : IsScalarTower V K F :=
      completeDVFRootFractionField_isScalarTower base varpi hvarpi N hN
    let : Algebra K₀ F := ((algebraMap K F).comp (algebraMap K₀ K)).toAlgebra
    ∀ (m : Ideal (F ⊗[K₀] L)) [m.IsMaximal],
      let P := GenericTensorFieldComponent m
      let : Algebra Rn P := genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
      Algebra.Etale Rn (integralClosure Rn P) := by
  intro V Rn hDomain F aKF hVKF aK₀F m hm P aRP
  have : IsDiscreteValuationRing V := base.toDVF.valuationSubring_isDiscreteValuationRing
  have : IsFractionRing V K := base.toDVF.valuationSubring_isFractionRing
  have hvarpiPrime : Prime varpi := dvfUniformizer_prime base.toDVF varpi hvarpi
  have : IsDiscreteValuationRing Rn :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hN varpi hvarpiPrime
  have : IsScalarTower K₀ K F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpiPrime
  let n := genericTensorTowerIntermediateIdeal (K := K₀) (F := K) (F' := F) (L := L) m
  have : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal (K := K₀) (F := K) (F' := F) (L := L) m
  let L₀ := GenericTensorFieldComponent n
  have hDegree : Module.finrank K L₀ ∣ Module.finrank K₀ L :=
    genericTensorFieldComponent_finrank_dvd_of_isGalois n
  let G₂ := F ⊗[K] L₀
  let : Algebra Rn G₂ := genericTensorProductLeftScalarAlgebra
  have hWhole : Algebra.Etale Rn (integralClosure Rn G₂) :=
    (finiteEtale_completeDVFUniformizerRoot_normalization_of_degree_coprime
      (L := L₀) base p hp (hdegree.of_dvd_left hDegree)
      varpi hvarpi N hN (hDegree.trans hdiv)).2.1
  let q := genericTensorTowerSecondIdeal (K := K₀) (F := K) (F' := F) (L := L) m
  have : q.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal (K := K₀) (F := K) (F' := F) (L := L) m
  let Q := GenericTensorFieldComponent q
  let : Algebra Rn Q := genericTensorFieldComponentLeftScalarAlgebra (R := Rn) q
  have : Algebra.Etale Rn (integralClosure Rn Q) :=
    integralClosure_genericTensorFieldComponent_etale_of_product Rn K F L₀ hWhole q
  have : IsScalarTower Rn F P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Rn F Q := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e : Q ≃ₐ[F] P :=
    genericTensorTowerSecondComponentAlgEquiv
      (K := K₀) (F := K) (F' := F) (L := L) m
  exact Algebra.Etale.of_equiv ((e.restrictScalars Rn).mapIntegralClosure)

end EtaleFundamentalGroups.Kummer
