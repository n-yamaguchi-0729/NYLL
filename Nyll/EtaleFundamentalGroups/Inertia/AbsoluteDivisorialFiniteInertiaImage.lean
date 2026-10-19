/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationInertiaImage
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteDivisorialFiniteQuotientNaturality

/-!
# The full absolute-inertia image in the same pointed finite cover

The selected generic lift determines the finite field embedding and the
literal contracted prime. The actual pointed deck quotient maps the absolute
inertia onto precisely the inertia at this contracted prime.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem fieldGeometricPoint_comp_genericExtensionMorphism'
    (U : Scheme.{u}) [IsIntegral U]
    (Omega : Type u) [Field Omega] [Algebra U.functionField Omega] :
    ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Omega := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1


section AbsoluteNormalizationPrime

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
  [IsLocallyNoetherian U] [ConnectedSpace U]
variable (Omega : Type u) [Field Omega]
  [Algebra U.functionField Omega]
  [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Algebra A U.functionField] [IsFractionRing A U.functionField]
  [Algebra A Omega] [IsScalarTower A U.functionField Omega]

local instance finiteImageAbsoluteNormalizationPrimeAction :
    MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
  IsIntegralClosure.MulSemiringAction A U.functionField Omega
    (integralClosure A Omega)


/-- Every inertia element at the selected finite normalization prime comes
from absolute inertia through the actual pointed deck quotient. -/
theorem finiteEtaleGaloisCoverQuotient_absoluteInertia_image
    (Q : Ideal (integralClosure A Omega)) [Q.IsPrime]
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W) :
    letI : IsGalois W := hW
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale W hW
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
    let x := (absoluteGenericFiberIso U Omega).inv.app W w
    let g := genericPointLiftRebase h W
      (fiberObjEquivHom
        (ξ K Omega ≫ U.genericExtensionMorphism K) W x)
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    letI : Algebra L Omega := j.toRingHom.toAlgebra
    letI : IsScalarTower K L Omega := by
      apply IsScalarTower.of_algebraMap_eq'
      ext z
      exact (j.commutes z).symm
    letI : IsScalarTower A L Omega := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      change algebraMap A Omega a = j (algebraMap A L a)
      calc
        algebraMap A Omega a =
            algebraMap K Omega (algebraMap A K a) :=
          IsScalarTower.algebraMap_apply A K Omega a
        _ = j (algebraMap K L (algebraMap A K a)) :=
          (j.commutes (algebraMap A K a)).symm
        _ = j (algebraMap A L a) := by
          rw [IsScalarTower.algebraMap_apply A K L]
    let B := integralClosure A L
    let QL := absoluteNormalizationPrimeContraction
      (A := A) (L := L) (Omega := Omega) Q
    letI : IsFractionRing B L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L B
    letI : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction A K L B
    letI : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
      Kummer.finiteEtaleGaloisCoverNormalizationAction W hW A B
    ∀ τ : (Aut W)ᵐᵒᵖ,
      τ ∈ QL.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ ↔
        ∃ sigma : Gal(Omega/K),
          sigma ∈ Q.toAddSubgroup.inertia Gal(Omega/K) ∧
          finiteEtaleGaloisCoverQuotientMonoidHom
            (U.genericExtensionMorphism Omega) W hW w
            (absoluteGenericGaloisToFundamentalGroup U Omega sigma) = τ := by
  let : IsGalois W := hW
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale W hW
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
  let x := (absoluteGenericFiberIso U Omega).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom
      (ξ K Omega ≫ U.genericExtensionMorphism K) W x)
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Omega := j.toRingHom.toAlgebra
  let : IsScalarTower K L Omega := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (j.commutes z).symm
  let : IsScalarTower A L Omega := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap A Omega a = j (algebraMap A L a)
    calc
      algebraMap A Omega a =
          algebraMap K Omega (algebraMap A K a) :=
        IsScalarTower.algebraMap_apply A K Omega a
      _ = j (algebraMap K L (algebraMap A K a)) :=
        (j.commutes (algebraMap A K a)).symm
      _ = j (algebraMap A L a) := by
        rw [IsScalarTower.algebraMap_apply A K L]
  let B := integralClosure A L
  let QL := absoluteNormalizationPrimeContraction
    (A := A) (L := L) (Omega := Omega) Q
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
    Kummer.finiteEtaleGaloisCoverNormalizationAction W hW A B
  change ∀ τ : (Aut W)ᵐᵒᵖ,
    τ ∈ QL.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ ↔
      ∃ sigma : Gal(Omega/K),
        sigma ∈ Q.toAddSubgroup.inertia Gal(Omega/K) ∧
        finiteEtaleGaloisCoverQuotientMonoidHom
          (U.genericExtensionMorphism Omega) W hW w
          (absoluteGenericGaloisToFundamentalGroup U Omega sigma) = τ
  intro τ
  constructor
  · intro hτ
    have hfield : finiteEtaleAutOpFunctionFieldMulEquiv W hW τ ∈
        QL.toAddSubgroup.inertia Gal(L/K) := by
      intro b
      have hb := hτ b
      rw [← Kummer.finiteEtaleGaloisCoverNormalizationAction_smul
        W hW A B τ b] at hb
      exact hb
    have himage := absoluteNormalizationPrime_inertia_map_eq_contraction
      (A := A) (K := K) (L := L) (Ω := Omega) Q
    have hmem : finiteEtaleAutOpFunctionFieldMulEquiv W hW τ ∈
        (Q.inertia Gal(Omega/K)).map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L) := by
      rw [himage]
      exact hfield
    obtain ⟨sigma, hsigma, heq⟩ := hmem
    refine ⟨sigma, hsigma, ?_⟩
    apply (finiteEtaleAutOpFunctionFieldMulEquiv W hW).injective
    change finiteEtaleAutFunctionFieldAlgEquiv W
      (finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Omega) W hW w
        (absoluteGenericGaloisToFundamentalGroup U Omega sigma)).unop = _
    exact (restrictNormalHom_eq_finiteEtaleAutFunctionFieldAlgEquiv_absoluteGenericGalois_rebased
      Omega W hW w sigma).symm.trans heq
  · rintro ⟨sigma, hsigma, rfl⟩
    exact finiteEtaleGaloisCoverQuotient_absoluteGenericGalois_mem_contractedIdealInertia
      Omega Q W hW w sigma hsigma

end AbsoluteNormalizationPrime

end EtaleFundamentalGroups.Inertia
