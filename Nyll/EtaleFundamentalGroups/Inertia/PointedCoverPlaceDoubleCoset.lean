/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteDivisorialFiniteQuotientNaturality
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPlaceDoubleCoset

/-!
# Actual place fibres of the same pointed finite Galois cover

The original absolute prime and geometric lift determine the finite place
and the double-coset equivalence, with no replacement of arithmetic data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve IsDedekindDomain
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem genericExtension_point_comp
    (U : Scheme.{u}) [IsIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω] :
    ξ U.functionField Ω ≫ U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Ω := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
  [IsLocallyNoetherian U] [ConnectedSpace U]
  (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
  [IsSepClosure U.functionField Ω] [IsSepClosed Ω]

variable {k : Type u} [Field k] [IsAlgClosed k]
  [Algebra k U.functionField] [IsCurveOver k U.functionField]
  (v : Place k U.functionField) [Algebra v.toValuationSubring Ω]
  [IsScalarTower v.toValuationSubring U.functionField Ω]

local instance pointedAbsolutePlaceAction :
    MulSemiringAction Gal(Ω/U.functionField) (integralClosure v.toValuationSubring Ω) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring U.functionField Ω _

/-- The place fibre of the actual pointed cover is the double-coset space
of its original absolute-inertia image and its actual finite quotient kernel. -/
def pointedCoverPlaceDoubleCosetEquiv
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime]
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    letI : IsGalois W := hW
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L := isGalois_functionField_of_isGalois_finiteEtale W hW
    let h := genericExtension_point_comp U Ω
    let x := (absoluteGenericFiberIso U Ω).inv.app W w
    let g := genericPointLiftRebase h W
      (fiberObjEquivHom (ξ K Ω ≫ U.genericExtensionMorphism K) W x)
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    letI : Algebra L Ω := j.toRingHom.toAlgebra
    letI : IsScalarTower K L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext z
      exact (j.commutes z).symm
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower v.toValuationSubring L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      change algebraMap v.toValuationSubring Ω a = j (algebraMap v.toValuationSubring L a)
      calc
        algebraMap v.toValuationSubring Ω a =
            algebraMap K Ω (algebraMap v.toValuationSubring K a) :=
          IsScalarTower.algebraMap_apply v.toValuationSubring K Ω a
        _ = j (algebraMap K L (algebraMap v.toValuationSubring K a)) :=
          (j.commutes (algebraMap v.toValuationSubring K a)).symm
        _ = j (algebraMap v.toValuationSubring L a) := by
          rw [IsScalarTower.algebraMap_apply v.toValuationSubring K L]
    let ρ := finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w
    ∀ (P : HeightOneSpectrum (Place.integralClosureAt L v)),
      P.asIdeal = absoluteNormalizationPrimeContraction
        (A := v.toValuationSubring) (L := L) (Omega := Ω) Q →
      DoubleCoset.Quotient (ρ.ker : Set π₁ᵉᵗ(U.genericExtensionMorphism Ω))
        ((Q.inertia Gal(Ω/K)).map (absoluteGenericGaloisToFundamentalGroup U Ω) :
          Set π₁ᵉᵗ(U.genericExtensionMorphism Ω)) ≃ Place.galoisPlaceFiber (L := L) v := by
  let : IsGalois W := hW
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L := isGalois_functionField_of_isGalois_finiteEtale W hW
  let h := genericExtension_point_comp U Ω
  let x := (absoluteGenericFiberIso U Ω).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom (ξ K Ω ≫ U.genericExtensionMorphism K) W x)
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Ω := j.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (j.commutes z).symm
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower v.toValuationSubring L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap v.toValuationSubring Ω a = j (algebraMap v.toValuationSubring L a)
    calc
      algebraMap v.toValuationSubring Ω a =
          algebraMap K Ω (algebraMap v.toValuationSubring K a) :=
        IsScalarTower.algebraMap_apply v.toValuationSubring K Ω a
      _ = j (algebraMap K L (algebraMap v.toValuationSubring K a)) :=
        (j.commutes (algebraMap v.toValuationSubring K a)).symm
      _ = j (algebraMap v.toValuationSubring L a) := by
        rw [IsScalarTower.algebraMap_apply v.toValuationSubring K L]
  let ρ := finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom
    (U.genericExtensionMorphism Ω) W hW w
  change ∀ (P : HeightOneSpectrum (Place.integralClosureAt L v)),
    P.asIdeal = absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q →
    DoubleCoset.Quotient (ρ.ker : Set π₁ᵉᵗ(U.genericExtensionMorphism Ω))
      ((Q.inertia Gal(Ω/K)).map (absoluteGenericGaloisToFundamentalGroup U Ω) :
        Set π₁ᵉᵗ(U.genericExtensionMorphism Ω)) ≃ Place.galoisPlaceFiber (L := L) v
  intro P hP
  have hρ : Function.Surjective ρ :=
    finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_surjective
      (U.genericExtensionMorphism Ω) W hW w
  have hcomp : ρ.comp (absoluteGenericGaloisToFundamentalGroup U Ω) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L := by
    apply MonoidHom.ext
    intro σ
    exact (finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_apply
      (U.genericExtensionMorphism Ω) W hW w
      (absoluteGenericGaloisToFundamentalGroup U Ω σ)).trans
        (restrictNormalHom_eq_finiteEtaleAutFunctionFieldAlgEquiv_absoluteGenericGalois_rebased
          Ω W hW w σ).symm
  exact normalizationPlaceDoubleCosetEquiv v
    (absoluteGenericGaloisToFundamentalGroup U Ω) ρ hρ hcomp Q P hP

end EtaleFundamentalGroups.Inertia
