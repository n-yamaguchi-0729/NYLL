/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.PrescribedRootTame
import Nyll.SchemeTheory.RingTheory.GenericFiber.FractionRing
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tame normalization after a prescribed higher uniformizer root

The finite étale unit factor constructed from tame valuation data remains
finite étale after changing the ramification-index root to a prescribed
divisible root. Its generic field is identified with the actual
compositum inside the fixed algebraic closure. Selecting that field from
the finite étale base change gives its literal finite étale normalization.

The lower factor, the root maps, their coefficient and generator
identities, and the final normalization property are all constructed.
The existing generic-fibre and compositum theorems are used without any
characteristic-zero hypothesis. This supplies the tame counterpart of
the local actual-factor calculation for Stacks Project 58.30.3:
https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

private theorem actualHigherFactor_of_unitFactor
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring) (hvarpi : Prime varpi)
    (pi : target.valuationSubring)
    (N : ℕ) (hN : 0 < N) (hdiv : ramificationIndex base target ∣ N)
    (beta : AlgebraicClosure L)
    (hbeta : beta ^ N = algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    Nonempty (HigherRadicalActualFactorData base target varpi N beta) := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let e := ramificationIndex base target
  let alpha := beta ^ (N / e)
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  have he : 0 < e := by
    apply Nat.pos_of_ne_zero
    simpa only [e, ramificationIndex] using
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
        (maximalIdeal_map_integerMap_ne_bot base target)
        (IsLocalRing.maximalIdeal.isMaximal W).isPrime
        (maximalIdeal_map_integerMap_le base target))
  have halpha : alpha ^ e = algebraMap K (AlgebraicClosure L) (varpi : K) := by
    change (beta ^ (N / e)) ^ e = algebraMap K (AlgebraicClosure L) (varpi : K)
    rw [← pow_mul, Nat.div_mul_cancel hdiv, hbeta]
  have : IsDiscreteValuationRing V := base.valuationSubring_isDiscreteValuationRing
  have : IsFractionRing V K := base.valuationSubring_isFractionRing
  have : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
  let F := lowerRadicalField (K := K) e N beta
  let E := targetCompositumOverLowerRadical (K := K) (L := L) e N beta
  let K' := higherRadicalFieldOverLower (K := K) e N beta
  let M := higherRadicalActualCompositumField (K := K) (L := L) e N beta
  let T := AdjoinRoot factor.q
  let : Algebra V F := ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
  let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
    pureRadicalGenericFiberAlgEquiv he varpi hvarpi alpha halpha
  have : IsDomain Rₑ := isDomain_adjoinRoot_X_pow_sub_C_of_prime he varpi hvarpi
  let : Algebra Rₑ F := (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
  have : IsFractionRing Rₑ F := isFractionRing_of_genericFiberAlgEquiv eRₑ
  let : Algebra Rₑ T := factor.radicalToUnitFactor.toRingHom.toAlgebra
  have : Algebra.Etale Rₑ T := factor.radical_etale
  have : Module.Finite W T := factor.q_finite
  have : Module.Finite V T := Module.Finite.trans W T
  have : IsScalarTower V Rₑ T :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (factor.radicalToUnitFactor.commutes z).symm
  have : Module.Finite Rₑ T := Module.Finite.of_restrictScalars_finite V Rₑ T
  let eGeneric : (F ⊗[Rₑ] T) ≃ₐ[F] E :=
    lowerUnitFactorGenericFiberAlgEquiv base target varpi pi N beta he hvarpi halpha factor
  have : Module.Finite F (F ⊗[Rₑ] T) := Module.Finite.base_change Rₑ F T
  have : FiniteDimensional F E := Module.Finite.equiv eGeneric.toLinearEquiv
  let : Algebra K K' := ((algebraMap F K').comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F K' := IsScalarTower.of_algebraMap_eq' rfl
  let Kₙ := IntermediateField.adjoin K ({beta} : Set (AlgebraicClosure L))
  let eKₙ : Kₙ ≃ₐ[K] K' :=
    { toFun := fun z ↦ ⟨z.1, z.2⟩
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl
      commutes' := fun _ ↦ rfl }
  let eRₙ : (K ⊗[V] Rₙ) ≃ₐ[K] K' :=
    (pureRadicalGenericFiberAlgEquiv hN varpi hvarpi beta hbeta).trans eKₙ
  have : IsDomain Rₙ := isDomain_adjoinRoot_X_pow_sub_C_of_prime hN varpi hvarpi
  have : IsDiscreteValuationRing Rₙ :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hN varpi hvarpi
  let : Algebra Rₙ K' := (genericFiberRightAlgHom eRₙ).toRingHom.toAlgebra
  have : IsFractionRing Rₙ K' := isFractionRing_of_genericFiberAlgEquiv eRₙ
  let higherMap : Rₑ →ₐ[V] Rₙ := adjoinRootPowerMapOfDvd hdiv varpi
  let : Algebra Rₑ Rₙ := higherMap.toRingHom.toAlgebra
  let : Algebra Rₑ K' := ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
  have : IsScalarTower Rₑ F K' := IsScalarTower.of_algebraMap_eq' rfl
  have hHigherRoot :
      ((genericFiberRightAlgHom eRₙ (AdjoinRoot.root (X ^ N - C varpi)) : K') :
        AlgebraicClosure L) = beta := by
    change ((pureRadicalGenericFiberAlgEquiv hN varpi hvarpi beta hbeta
      (1 ⊗ₜ[V] AdjoinRoot.root (X ^ N - C varpi)) : Kₙ) : AlgebraicClosure L) = beta
    exact congrArg Subtype.val
      (pureRadicalGenericFiberAlgEquiv_tmul_root hN varpi hvarpi beta hbeta)
  have hLowerRoot :
      ((genericFiberRightAlgHom eRₑ (AdjoinRoot.root (X ^ e - C varpi)) : F) :
        AlgebraicClosure L) = alpha := by
    exact congrArg Subtype.val
      (pureRadicalGenericFiberAlgEquiv_tmul_root he varpi hvarpi alpha halpha)
  have hHigherBase (z : V) :
      ((genericFiberRightAlgHom eRₙ (algebraMap V Rₙ z) : K') : AlgebraicClosure L) =
        algebraMap K (AlgebraicClosure L) (z : K) := by
    rw [(genericFiberRightAlgHom eRₙ).commutes]
    rfl
  have hLowerBase (z : V) :
      ((algebraMap F K' (genericFiberRightAlgHom eRₑ (algebraMap V Rₑ z)) : K') :
        AlgebraicClosure L) = algebraMap K (AlgebraicClosure L) (z : K) := by
    rw [(genericFiberRightAlgHom eRₑ).commutes]
    rfl
  have hMaps : (genericFiberRightAlgHom eRₙ).toRingHom.comp higherMap.toRingHom =
      (algebraMap F K').comp (genericFiberRightAlgHom eRₑ).toRingHom :=
    higherRoot_genericMaps_comp_eq F K' varpi hdiv
      (genericFiberRightAlgHom eRₙ).toRingHom (genericFiberRightAlgHom eRₑ).toRingHom
      (fun z ↦ (hHigherBase z).trans (hLowerBase z).symm)
      beta alpha hHigherRoot hLowerRoot rfl
  have : IsScalarTower Rₑ Rₙ K' :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (DFunLike.congr_fun hMaps z).symm
  let kToM : K' →ₐ[F] M := IntermediateField.inclusion (show K' ≤ M from le_sup_right)
  let : Algebra K' M := kToM.toRingHom.toAlgebra
  have : IsScalarTower V Rₙ K' :=
    IsScalarTower.of_algebraMap_eq fun z ↦ ((genericFiberRightAlgHom eRₙ).commutes z).symm
  have : IsScalarTower V K' M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V F K' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V F M := IsScalarTower.of_algebraMap_eq' rfl
  let phi : Rₙ →+* M := kToM.toRingHom.comp (genericFiberRightAlgHom eRₙ).toRingHom
  let : Algebra Rₙ M := phi.toAlgebra
  have hEtale : Algebra.Etale Rₙ (integralClosure Rₙ M) :=
    integralClosure_compositum_etale_of_finiteEtale_baseChange
      (A := Rₑ) (B := Rₙ) (T := T) E K' eGeneric
  refine ⟨{
    rootMap := phi
    commutes_coe := ?_
    root_coe := ?_
    etale_normalization := hEtale }⟩
  · exact hHigherBase
  · exact hHigherRoot

/-- Tame valuation data constructs the normalization of the actual
compositum after any prescribed positive root divisible by the
ramification index. The normalization and its root coordinates are
conclusions, with no characteristic-zero or perfect-residue assumption. -/
theorem higherRadicalActualFactorData_of_tame
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable base.residueField target.residueField]
    (heUnit : IsUnit (ramificationIndex base target : base.valuationSubring))
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (pi : target.valuationSubring) (unit : target.valuationSubringˣ)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hdecomp : integerMap base target varpi =
      (unit : target.valuationSubring) * pi ^ ramificationIndex base target)
    (N : ℕ) (hN : 0 < N) (hdiv : ramificationIndex base target ∣ N)
    (beta : AlgebraicClosure L)
    (hbeta : beta ^ N = algebraMap K (AlgebraicClosure L) (varpi : K)) :
    Nonempty (HigherRadicalActualFactorData base target varpi N beta) := by
  let e := ramificationIndex base target
  let alpha := beta ^ (N / e)
  have halphaPow : alpha ^ e = algebraMap K (AlgebraicClosure L) (varpi : K) := by
    change (beta ^ (N / e)) ^ e = algebraMap K (AlgebraicClosure L) (varpi : K)
    rw [← pow_mul, Nat.div_mul_cancel hdiv, hbeta]
  obtain ⟨delta, q, unitFactorEquiv, radicalToUnitFactor, _hdelta, halpha,
      hqMonic, hqMap, _hqDvd, hqFinite, hqEtale, hCompositum,
      hFactorRoot, hRadicalRoot, hRootFiniteEtale⟩ :=
    exists_finiteEtale_unitFactor_for_prescribed_tame_uniformizerRoot
      base target heUnit varpi hvarpi pi unit hpi hdecomp alpha halphaPow
  let factor : HigherRadicalUnitFactorData base target varpi pi N beta :=
    { delta := delta
      q := q
      unitFactorEquiv := unitFactorEquiv
      radicalToUnitFactor := radicalToUnitFactor
      alpha_eq := halpha
      q_monic := hqMonic
      q_map := hqMap
      q_etale := hqEtale
      q_finite := hqFinite
      compositum_eq := hCompositum
      unitFactor_root := hFactorRoot
      radical_root := hRadicalRoot
      radical_etale := hRootFiniteEtale.2 }
  have hvarpiPrime : Prime varpi := by
    have hne : varpi ≠ 0 := fun hz ↦ hvarpi.ne_zero (congrArg Subtype.val hz)
    apply (Ideal.span_singleton_prime hne).mp
    rw [← Valuation.IsUniformizer.is_generator hvarpi]
    exact (IsLocalRing.maximalIdeal.isMaximal base.valuationSubring).isPrime
  exact actualHigherFactor_of_unitFactor base target varpi hvarpiPrime pi N hN hdiv beta
    hbeta factor

end EtaleFundamentalGroups.Kummer
