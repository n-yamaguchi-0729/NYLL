/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.LocalArtinAction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# One absolute Artin representative on all original pointed covers

The coefficient comparison retains an arbitrary original embedding of a
finite abelian extension into the fixed separable closure. Its actual image
field supplies the finite restriction of absolute reciprocity. Restriction
back through the original embedding gives native finite reciprocity.

Consequently every representative of the entire absolute Artin value gives
the correct deck action on every pointed finite abelian cover. The final
existence statement chooses the representative once, before all covers and
their points, and keeps its equality with the original absolute Artin value.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicCurve LocalClassFieldTheory

namespace FunctionField

variable (k : Type v) (K : Type u) (L : Type w) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Any representative of the entire absolute Artin value has the native
finite Artin restriction through every prescribed original embedding. -/
theorem absoluteArtin_lift_coefficient
    (c : IdeleClassGroup k K) (σ : Gal(SeparableClosure K/K))
    (hσ : localAbsoluteAbelianizationQuotientMap K σ = absoluteArtin k K c)
    (i : L →ₐ[K] SeparableClosure K) (a : L) :
    σ (i a) = i (abelianFiniteArtin k K L c a) := by
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) Ω :=
    ((algebraMap K Ω).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) Ω :=
    IsScalarTower.of_algebraMap_eq fun x =>
      congrArg (algebraMap K Ω) (IsScalarTower.algebraMap_apply k (RatFunc k) K x)
  let E : IntermediateField K Ω := i.fieldRange
  let e : L ≃ₐ[K] E := i.equivFieldRange
  have hEfinite : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  have hEabelian : IsAbelianGalois K E := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hEprincipal : HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  let aLE : Algebra L E := e.toRingHom.toAlgebra
  have hKLE : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  have hE : AlgEquiv.restrictNormalHom E σ = abelianFiniteArtin k K E c := by
    calc
      AlgEquiv.restrictNormalHom E σ =
          absoluteAbelianRestriction K E
            (localAbsoluteAbelianizationQuotientMap K σ) :=
        (absoluteAbelianRestriction_mk K E σ).symm
      _ = absoluteAbelianRestriction K E (absoluteArtin k K c) :=
        congrArg (absoluteAbelianRestriction K E) hσ
      _ = abelianFiniteArtin k K E c := absoluteArtin_restriction k K E c
  have hL : AlgEquiv.restrictNormalHom L (abelianFiniteArtin k K E c) =
      abelianFiniteArtin k K L c := abelianFiniteArtin_restrictNormal k K L E c
  calc
    σ (i a) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ (e a)) :=
      (AlgEquiv.restrictNormal_commutes σ E (e a)).symm
    _ = algebraMap E Ω (abelianFiniteArtin k K E c (e a)) := by rw [hE]
    _ = algebraMap E Ω
        (e (AlgEquiv.restrictNormalHom L (abelianFiniteArtin k K E c) a)) :=
      congrArg (algebraMap E Ω)
        (AlgEquiv.restrictNormal_commutes (abelianFiniteArtin k K E c) L a).symm
    _ = i (abelianFiniteArtin k K L c a) := by rw [hL]; rfl

end FunctionField

namespace EtaleFundamentalGroups

open FunctionField Inertia

attribute [local instance] finiteCoverIdeleClassMulOneClass finiteCoverIdeleClassGroup

private abbrev coverAbsoluteArtinValue (k : Type v) (K : Type u)
    [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] (c : IdeleClassGroup k K) : localAbsoluteAbelianProfinite K :=
  absoluteArtin k K c

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (k : Type v) [Field k] [Finite k] [Algebra k U.functionField]
    [Algebra (RatFunc k) U.functionField] [IsScalarTower k (RatFunc k) U.functionField]
    [FunctionField k U.functionField]

attribute [local instance] basePrincipalDivisors

/-- The entire absolute Artin value determines the action on the original
cover at every chosen generic fibre point, through its literal embedding. -/
theorem absoluteArtin_lift_pointedCover
    (c : IdeleClassGroup k U.functionField)
    (σ : Gal(SeparableClosure U.functionField/U.functionField))
    (hσ : localAbsoluteAbelianizationQuotientMap U.functionField σ =
      coverAbsoluteArtinValue k U.functionField c)
    (W : FiniteEtale U) [IsGalois W] :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField := coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField := coverPrincipalDivisors W k
    ∀ [IsAbelianGalois U.functionField W.left.functionField]
      (w : (fiber (U.genericExtensionMorphism (SeparableClosure U.functionField))).obj W),
    finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism (SeparableClosure U.functionField)) W inferInstance w
        (absoluteGenericGaloisToFundamentalGroup U (SeparableClosure U.functionField) σ) =
      finiteEtaleCoverArtin W k c := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    habelian w
  have hcoeff (a : W.left.functionField) :
      σ (finiteEtaleFiberPointFunctionFieldAlgHom W w a) =
        finiteEtaleFiberPointFunctionFieldAlgHom W w
          (abelianFiniteArtin k U.functionField W.left.functionField c a) :=
    absoluteArtin_lift_coefficient k U.functionField W.left.functionField c σ hσ
      (finiteEtaleFiberPointFunctionFieldAlgHom W w) a
  exact (finiteEtaleCoverArtin_quotient_eq_iff W k
    (SeparableClosure U.functionField) w c σ).mpr hcoeff

/-- A single actual generic Galois representative realizes the entire
absolute Artin value and the native action on all original pointed finite
abelian covers simultaneously. The representative is chosen before the cover. -/
theorem exists_absoluteArtin_pointedCover_lift
    (c : IdeleClassGroup k U.functionField) :
    ∃ σ : Gal(SeparableClosure U.functionField/U.functionField),
      localAbsoluteAbelianizationQuotientMap U.functionField σ =
          coverAbsoluteArtinValue k U.functionField c ∧
      ∀ (W : FiniteEtale U) [IsGalois W],
        let _ : IsIntegral W.left := coverIntegral W
        let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W
        let _ : FiniteDimensional U.functionField W.left.functionField :=
          coverFieldFinite W
        let _ : Algebra k W.left.functionField :=
          ((algebraMap U.functionField W.left.functionField).comp
            (algebraMap k U.functionField)).toAlgebra
        let _ : IsScalarTower k U.functionField W.left.functionField :=
          IsScalarTower.of_algebraMap_eq fun _ => rfl
        let _ : HasPrincipalDivisors k W.left.functionField :=
          coverPrincipalDivisors W k
        ∀ [IsAbelianGalois U.functionField W.left.functionField]
          (w : (fiber (U.genericExtensionMorphism (SeparableClosure U.functionField))).obj W),
        finiteEtaleGaloisCoverQuotientMonoidHom
            (U.genericExtensionMorphism (SeparableClosure U.functionField)) W inferInstance w
            (absoluteGenericGaloisToFundamentalGroup U (SeparableClosure U.functionField) σ) =
          finiteEtaleCoverArtin W k c := by
  obtain ⟨σ, hσ⟩ := (QuotientGroup.mk'_surjective
    (commutator (intrinsicAbsoluteGalois U.functionField)).topologicalClosure)
    (coverAbsoluteArtinValue k U.functionField c)
  refine ⟨σ, hσ, ?_⟩
  intro W hW integralCover coverAlgebra finiteCover coverConstants coverConstantTower
    coverDivisors habelian w
  exact absoluteArtin_lift_pointedCover k c σ hσ W w

end EtaleFundamentalGroups
