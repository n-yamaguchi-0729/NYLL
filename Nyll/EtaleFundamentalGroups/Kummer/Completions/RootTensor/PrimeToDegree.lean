/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.ComponentPrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.TameUniformizerRoot
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.ActualCompositum.TensorComponent
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRFiniteEtaleAlgebra
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.IntegralClosure
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Complete normalization at an exponent divisible by a prime-to-p degree

The valuation extension is constructed from the actual integral closure of
the complete base DVR. Its finiteness then supplies both residue separability
and the tame ramification index used in every literal tensor component.
The canonical product decomposition assembles their normalizations into
the normalization of the original tensor product.

The conclusion includes finiteness and recovery of the entire generic
fibre. There is no input asserting that a component normalization is étale.
The exponent can be the extension degree itself; more generally, any
positive multiple of that degree works for the normalization calculation.
This is the complete local tame calculation used in Stacks Project 58.30.3:
https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uL

/-- A finite separable extension of degree prime to the residue
characteristic has finite étale normalization after a uniformizer root
whose exponent is a positive multiple of its degree. The valuation
extension and every component normalization are constructed internally. -/
theorem finiteEtale_completeDVFUniformizerRoot_normalization_of_degree_coprime
    {K : Type uK} {L : Type uL} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : CompleteDVF.{uK, uV} K)
    (p : ℕ) (hp : p.Prime) [CharP base.residueField p]
    (hdegree : Nat.Coprime (Module.finrank K L) p)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) (hdiv : Module.finrank K L ∣ N) :
    let V := base.valuationSubring
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let : IsDomain Rn := completeDVFRootRing_isDomain base varpi hvarpi N hN
    let F := FractionRing Rn
    let : Algebra K F := completeDVFRootFractionFieldAlgebra base varpi hvarpi N hN
    let : IsScalarTower V K F :=
      completeDVFRootFractionField_isScalarTower base varpi hvarpi N hN
    let G := F ⊗[K] L
    let : Algebra Rn G := genericTensorProductLeftScalarAlgebra
    Module.Finite Rn (integralClosure Rn G) ∧
      Algebra.Etale Rn (integralClosure Rn G) ∧
        Nonempty (F ⊗[Rn] integralClosure Rn G ≃ₐ[F] G) := by
  intro V Rn hDomain F aKF hTower G aRnG
  obtain ⟨target, hExt, hIntegral⟩ :=
    exists_integralClosure_standard_fundamental_identity (K := K) (L := L) base
  have : base.valuation.HasExtension target.valuation := hExt
  have : IsIntegralClosure target.valuationSubring V L := hIntegral.1
  have : IsScalarTower V target.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite V target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_isIntegralClosure (K := K) (L := L) base target
  have hEtale : Algebra.Etale Rn (integralClosure Rn G) := by
    apply integralClosure_genericTensorProduct_etale
    intro m hm
    let P := GenericTensorFieldComponent m
    let aRoot : Algebra Rn P :=
      pureRadicalFractionFieldGenericTensorComponentRootAlgebra (K := K) varpi m
    have hRoot :
        let : Algebra Rn P := aRoot
        Algebra.Etale Rn (integralClosure Rn P) :=
      integralClosure_uniformizerTensorComponent_etale_of_degree_coprime
        base.toDVF target.toDVF p hp hdegree varpi hvarpi N hN hdiv m
    let aLeft : Algebra Rn P := genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
    have hAlgebra : aRoot = aLeft := by
      apply Algebra.algebra_ext
      intro r
      rfl
    have hLeft :
        let : Algebra Rn P := aLeft
        Algebra.Etale Rn (integralClosure Rn P) := hAlgebra ▸ hRoot
    exact hLeft
  have : Algebra.FinitePresentation Rn (integralClosure Rn G) := hEtale.finitePresentation
  have hFiniteType : Algebra.FiniteType Rn (integralClosure Rn G) :=
    Algebra.FiniteType.of_finitePresentation (R := Rn) (A := integralClosure Rn G)
  have hFinite : Module.Finite Rn (integralClosure Rn G) :=
    Algebra.IsIntegral.finite (R := Rn) (A := integralClosure Rn G) (h' := hFiniteType)
  have : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  have : Module.Finite F G := Module.Finite.base_change K F L
  have : Algebra.Etale F G := inferInstance
  have : IsScalarTower Rn F G :=
    TensorProduct.isScalarTower_left (R := K) (R'₂ := Rn) (R' := F)
  exact ⟨hFinite, hEtale, ⟨SchemeTheory.integralClosureFiniteEtaleGenericFiberEquiv Rn F G⟩⟩

end EtaleFundamentalGroups.Kummer
