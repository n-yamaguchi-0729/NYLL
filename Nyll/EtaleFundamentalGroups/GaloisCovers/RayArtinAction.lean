/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.AbsoluteArtinAction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReciprocity
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayLocalArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteAbelianQuotientKernels
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteGenericGaloisSurjectivity
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# The absolute ray quotient acting on original pointed abelian covers

The literal embedding selected by a generic fibre point defines restriction
from the absolute abelian Galois group to the original covering field. Its
deck action is exactly the original pointed fundamental-group quotient.

The Artin image of a ray congruence subgroup acts trivially on this cover
exactly when its actual extension conductor is bounded by the modulus.
The resulting ray-quotient action is surjective and agrees on every actual
restricted ray family with finite reciprocity. This finite comparison does
not identify a reduced ray quotient with the full affine etale group.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicCurve LocalClassFieldTheory

namespace FunctionField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Transport of an automorphism of the literal image field back through
the original embedding, with no choice of a different field embedding. -/
private def embeddingRangeAutRestriction (i : L →ₐ[K] SeparableClosure K) :
    Gal(i.fieldRange/K) →* Gal(L/K) where
  toFun σ := i.equivFieldRange.trans (σ.trans i.equivFieldRange.symm)
  map_one' := by
    apply AlgEquiv.ext
    intro a
    exact i.equivFieldRange.symm_apply_apply a
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro a
    change i.equivFieldRange.symm (σ (τ (i.equivFieldRange a))) =
      i.equivFieldRange.symm
        (σ (i.equivFieldRange (i.equivFieldRange.symm (τ (i.equivFieldRange a)))))
    rw [i.equivFieldRange.apply_symm_apply]

variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Absolute abelian restriction through a prescribed original embedding.
The topology and finite restriction are those of its actual image field. -/
def absoluteAbelianRestrictionViaEmbedding (i : L →ₐ[K] SeparableClosure K) :
    localAbsoluteAbelianProfinite K →ₜ* Gal(L/K) := by
  have hfinite : FiniteDimensional K i.fieldRange :=
    i.equivFieldRange.toLinearEquiv.finiteDimensional
  have habelian : IsAbelianGalois K i.fieldRange :=
    IsAbelianGalois.of_algHom i.equivFieldRange.symm.toAlgHom
  refine
    { toMonoidHom := (embeddingRangeAutRestriction i).comp
        (absoluteAbelianRestriction K i.fieldRange).toMonoidHom
      continuous_toFun := ?_ }
  have htransport : Continuous (embeddingRangeAutRestriction i) :=
    continuous_of_discreteTopology
  exact htransport.comp (absoluteAbelianRestriction K i.fieldRange).continuous_toFun

/-- On an absolute representative, this restriction acts through the
literal coefficients of the selected embedding. -/
theorem absoluteAbelianRestrictionViaEmbedding_mk_coefficient
    (i : L →ₐ[K] SeparableClosure K) (σ : Gal(SeparableClosure K/K)) (a : L) :
    i (absoluteAbelianRestrictionViaEmbedding i
        (localAbsoluteAbelianizationQuotientMap K σ) a) = σ (i a) := by
  let E : IntermediateField K (SeparableClosure K) := i.fieldRange
  let e : L ≃ₐ[K] E := i.equivFieldRange
  have hfinite : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  have habelian : IsAbelianGalois K E := IsAbelianGalois.of_algHom e.symm.toAlgHom
  change i (e.symm (absoluteAbelianRestriction K E
    (localAbsoluteAbelianizationQuotientMap K σ) (e a))) = σ (i a)
  have hrestrict : absoluteAbelianRestriction K E
      (localAbsoluteAbelianizationQuotientMap K σ) = AlgEquiv.restrictNormalHom E σ :=
    absoluteAbelianRestriction_mk K E σ
  calc
    i (e.symm (absoluteAbelianRestriction K E
        (localAbsoluteAbelianizationQuotientMap K σ) (e a))) =
      i (e.symm (AlgEquiv.restrictNormalHom E σ (e a))) :=
        congrArg (fun τ : Gal(E/K) => i (e.symm (τ (e a)))) hrestrict
    i (e.symm (AlgEquiv.restrictNormalHom E σ (e a))) =
        algebraMap E (SeparableClosure K) (AlgEquiv.restrictNormalHom E σ (e a)) :=
      congrArg (fun x : E => (x : SeparableClosure K))
        (e.apply_symm_apply (AlgEquiv.restrictNormalHom E σ (e a)))
    _ = σ (algebraMap E (SeparableClosure K) (e a)) :=
      AlgEquiv.restrictNormal_commutes σ E (e a)
    _ = σ (i a) := rfl

/-- Restricting the entire absolute Artin value through the original
embedding recovers the native finite Artin automorphism. -/
theorem absoluteAbelianRestrictionViaEmbedding_artin
    (k : Type v) [Field k] [Finite k] [Algebra k K] [Algebra k L]
    [IsScalarTower k K L] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    (i : L →ₐ[K] SeparableClosure K) (c : IdeleClassGroup k K) :
    absoluteAbelianRestrictionViaEmbedding i (absoluteArtin k K c) =
      abelianFiniteArtin k K L c := by
  obtain ⟨σ, hσ⟩ := (QuotientGroup.mk'_surjective
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure) (absoluteArtin k K c)
  apply AlgEquiv.ext
  intro a
  apply i.injective
  have hσ' : localAbsoluteAbelianizationQuotientMap K σ = absoluteArtin k K c := hσ
  exact ((congrArg (fun γ : localAbsoluteAbelianProfinite K =>
      i (absoluteAbelianRestrictionViaEmbedding i γ a)) hσ').symm.trans
    (absoluteAbelianRestrictionViaEmbedding_mk_coefficient i σ a)).trans
      (absoluteArtin_lift_coefficient k K L c σ hσ i a)

/-- Abelian restriction is independent of the selected embedding. Equality
is proved on the dense image of actual reciprocity and then by continuity. -/
theorem absoluteAbelianRestrictionViaEmbedding_eq
    (k : Type v) [Field k] [Finite k] [Algebra k K] [Algebra k L]
    [IsScalarTower k K L] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    (i j : L →ₐ[K] SeparableClosure K) :
    absoluteAbelianRestrictionViaEmbedding i = absoluteAbelianRestrictionViaEmbedding j := by
  apply ContinuousMonoidHom.ext
  intro γ
  have hclosed : IsClosed {δ : localAbsoluteAbelianProfinite K |
      absoluteAbelianRestrictionViaEmbedding i δ =
        absoluteAbelianRestrictionViaEmbedding j δ} :=
    isClosed_eq (absoluteAbelianRestrictionViaEmbedding i).continuous_toFun
      (absoluteAbelianRestrictionViaEmbedding j).continuous_toFun
  have hrange : Set.range (absoluteArtin k K) ⊆
      {δ : localAbsoluteAbelianProfinite K |
        absoluteAbelianRestrictionViaEmbedding i δ =
          absoluteAbelianRestrictionViaEmbedding j δ} := by
    rintro δ ⟨c, rfl⟩
    exact (absoluteAbelianRestrictionViaEmbedding_artin k i c).trans
      (absoluteAbelianRestrictionViaEmbedding_artin k j c).symm
  exact closure_minimal hrange hclosed ((absoluteArtin_denseRange k K) γ)

end FunctionField

namespace EtaleFundamentalGroups

open FunctionField FunctionField.RayClass Inertia

attribute [local instance] finiteCoverIdeleClassMulOneClass finiteCoverIdeleClassGroup

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (W : FiniteEtale U) [IsGalois W]
    [coverAbelian : let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsAbelianGalois U.functionField W.left.functionField]
    (w : (fiber (U.genericExtensionMorphism (SeparableClosure U.functionField))).obj W)

/-- The actual pointed deck quotient, factored through the absolute
abelian Galois group by restriction through the same generic fibre point. -/
def finiteEtaleCoverAbsoluteAction :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    localAbsoluteAbelianProfinite U.functionField →* (Aut W)ᵐᵒᵖ := by
  intro integralCover coverAlgebra finiteCover
  exact
    (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm.toMonoidHom.comp
      (absoluteAbelianRestrictionViaEmbedding
        (finiteEtaleFiberPointFunctionFieldAlgHom W w)).toMonoidHom

/-- This is the original pointed quotient of the original generic Galois
map on each representative, with the chosen fibre point retained. -/
theorem finiteEtaleCoverAbsoluteAction_mk :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    ∀ (σ : Gal(SeparableClosure U.functionField/U.functionField)),
    finiteEtaleCoverAbsoluteAction W w
        (localAbsoluteAbelianizationQuotientMap U.functionField σ) =
      finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism (SeparableClosure U.functionField)) W inferInstance w
        (absoluteGenericGaloisToFundamentalGroup U (SeparableClosure U.functionField) σ) := by
  intro integralCover coverAlgebra finiteCover σ
  let e := finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance
  apply e.injective
  change e (e.symm (absoluteAbelianRestrictionViaEmbedding
    (finiteEtaleFiberPointFunctionFieldAlgHom W w)
      (localAbsoluteAbelianizationQuotientMap U.functionField σ))) = _
  rw [e.apply_symm_apply]
  apply AlgEquiv.ext
  intro a
  apply (finiteEtaleFiberPointFunctionFieldAlgHom W w).injective
  exact (absoluteAbelianRestrictionViaEmbedding_mk_coefficient
    (finiteEtaleFiberPointFunctionFieldAlgHom W w) σ a).trans
      (pointedCoverQuotient_coefficient W (SeparableClosure U.functionField) w σ a).symm

/-- Every actual deck automorphism is reached from the same absolute
abelian Galois group. -/
theorem finiteEtaleCoverAbsoluteAction_surjective :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    Function.Surjective (finiteEtaleCoverAbsoluteAction W w) := by
  intro integralCover coverAlgebra finiteCover τ
  obtain ⟨g, hg⟩ := finiteEtaleGaloisCoverQuotientMonoidHom_surjective
    (U.genericExtensionMorphism (SeparableClosure U.functionField)) W inferInstance w τ
  obtain ⟨σ, hσ⟩ := absoluteGenericGaloisToFundamentalGroup_surjective
    U (SeparableClosure U.functionField) g
  refine ⟨localAbsoluteAbelianizationQuotientMap U.functionField σ, ?_⟩
  rw [finiteEtaleCoverAbsoluteAction_mk, hσ, hg]

/-- The original pointed action has closed kernel in the actual Krull
quotient topology, without imposing a topology on the categorical deck group. -/
theorem isClosed_finiteEtaleCoverAbsoluteAction_ker :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    IsClosed ((finiteEtaleCoverAbsoluteAction W w).ker :
      Set (localAbsoluteAbelianProfinite U.functionField)) := by
  intro integralCover coverAlgebra finiteCover
  let r := absoluteAbelianRestrictionViaEmbedding
    (finiteEtaleFiberPointFunctionFieldAlgHom W w)
  have hker : (finiteEtaleCoverAbsoluteAction W w).ker = r.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective r.toMonoidHom
      (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm.toMonoidHom
      (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm.injective
  rw [hker]
  exact isClosed_eq r.continuous_toFun continuous_const

variable (k : Type v) [Field k] [Finite k] [Algebra k U.functionField]
    [Algebra (RatFunc k) U.functionField] [IsScalarTower k (RatFunc k) U.functionField]
    [FunctionField k U.functionField]

attribute [local instance] basePrincipalDivisors

/-- The absolute action on the original cover takes the entire absolute
Artin value to its original finite deck reciprocity value. -/
theorem finiteEtaleCoverAbsoluteAction_artin :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    let coverPresentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra
      k U.functionField W.left.functionField
    let _ : Algebra (RatFunc k) W.left.functionField := coverPresentation.val
    let _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      coverPresentation.property.1
    let _ : FunctionField k W.left.functionField := coverPresentation.property.2
    ∀ (c : IdeleClassGroup k U.functionField),
    finiteEtaleCoverAbsoluteAction W w (absoluteArtin k U.functionField c) =
      finiteEtaleCoverArtin W k c := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    coverPresentation coverRatFuncAlgebra coverRatFuncTower coverFunctionField c
  change (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
    (absoluteAbelianRestrictionViaEmbedding (finiteEtaleFiberPointFunctionFieldAlgHom W w)
      (absoluteArtin k U.functionField c)) =
    (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
      (abelianFiniteArtin k U.functionField W.left.functionField c)
  rw [absoluteAbelianRestrictionViaEmbedding_artin k]

include k in
/-- For an abelian cover the original action does not depend on the chosen
generic fibre point. The underlying finite Artin map supplies the comparison. -/
theorem finiteEtaleCoverAbsoluteAction_eq :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    let coverPresentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra
      k U.functionField W.left.functionField
    let _ : Algebra (RatFunc k) W.left.functionField := coverPresentation.val
    let _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      coverPresentation.property.1
    let _ : FunctionField k W.left.functionField := coverPresentation.property.2
    ∀ (w' : (fiber (U.genericExtensionMorphism (SeparableClosure U.functionField))).obj W),
    finiteEtaleCoverAbsoluteAction W w = finiteEtaleCoverAbsoluteAction W w' := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    coverPresentation coverRatFuncAlgebra coverRatFuncTower coverFunctionField w'
  apply MonoidHom.ext
  intro γ
  change (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
    (absoluteAbelianRestrictionViaEmbedding (finiteEtaleFiberPointFunctionFieldAlgHom W w) γ) =
    (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
      (absoluteAbelianRestrictionViaEmbedding (finiteEtaleFiberPointFunctionFieldAlgHom W w') γ)
  rw [absoluteAbelianRestrictionViaEmbedding_eq k
    (finiteEtaleFiberPointFunctionFieldAlgHom W w)
    (finiteEtaleFiberPointFunctionFieldAlgHom W w')]

/-- Triviality of the actual ray Artin subgroup on the original cover is
equivalent to the actual norm conductor bound. No cover comparison is an input. -/
theorem artinRaySubgroup_le_coverAction_ker_iff :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    let coverPresentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra
      k U.functionField W.left.functionField
    let _ : Algebra (RatFunc k) W.left.functionField := coverPresentation.val
    let _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      coverPresentation.property.1
    let _ : FunctionField k W.left.functionField := coverPresentation.property.2
    ∀ (m : RayClass.Modulus k U.functionField),
    artinRaySubgroup m ≤ (finiteEtaleCoverAbsoluteAction W w).ker ↔
      extensionConductor (k := k) (K := U.functionField) (L := W.left.functionField) ≤ m := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    coverPresentation coverRatFuncAlgebra coverRatFuncTower coverFunctionField m
  rw [extensionConductor_le_iff]
  constructor
  · intro h c hc
    have ha : finiteEtaleCoverAbsoluteAction W w (absoluteArtin k U.functionField c) = 1 :=
      h ⟨c, hc, rfl⟩
    rw [finiteEtaleCoverAbsoluteAction_artin] at ha
    have hc' : c ∈ (finiteEtaleCoverArtin W k).ker := ha
    rw [finiteEtaleCoverArtin_ker] at hc'
    exact hc'
  · rintro h γ ⟨c, hc, rfl⟩
    change finiteEtaleCoverAbsoluteAction W w (absoluteArtin k U.functionField c) = 1
    rw [finiteEtaleCoverAbsoluteAction_artin]
    change c ∈ (finiteEtaleCoverArtin W k).ker
    rw [finiteEtaleCoverArtin_ker]
    exact h hc

/-- The actual absolute ray quotient acts on every original pointed
abelian cover whose proved conductor is bounded by this modulus. -/
def finiteEtaleCoverRayAction :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    let coverPresentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra
      k U.functionField W.left.functionField
    let _ : Algebra (RatFunc k) W.left.functionField := coverPresentation.val
    let _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      coverPresentation.property.1
    let _ : FunctionField k W.left.functionField := coverPresentation.property.2
    have _ : _root_.IsGalois U.functionField W.left.functionField :=
      (show IsAbelianGalois U.functionField W.left.functionField from coverAbelian).toIsGalois
    ∀ (m : RayClass.Modulus k U.functionField)
    (_ : extensionConductor (k := k) (K := U.functionField)
      (L := W.left.functionField) ≤ m),
    localAbsoluteAbelianProfinite U.functionField ⧸ artinRaySubgroup m →* (Aut W)ᵐᵒᵖ := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    coverPresentation coverRatFuncAlgebra coverRatFuncTower coverFunctionField coverGalois m hm
  exact
    QuotientGroup.lift (artinRaySubgroup m) (finiteEtaleCoverAbsoluteAction W w)
      ((artinRaySubgroup_le_coverAction_ker_iff W w k m).mpr hm)

/-- Representatives retain the original cover action. -/
theorem finiteEtaleCoverRayAction_mk :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    let coverPresentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra
      k U.functionField W.left.functionField
    let _ : Algebra (RatFunc k) W.left.functionField := coverPresentation.val
    let _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      coverPresentation.property.1
    let _ : FunctionField k W.left.functionField := coverPresentation.property.2
    have _ : _root_.IsGalois U.functionField W.left.functionField :=
      (show IsAbelianGalois U.functionField W.left.functionField from coverAbelian).toIsGalois
    ∀ (m : RayClass.Modulus k U.functionField)
    (hm : extensionConductor (k := k) (K := U.functionField)
      (L := W.left.functionField) ≤ m)
    (γ : localAbsoluteAbelianProfinite U.functionField),
    finiteEtaleCoverRayAction W w k m hm (QuotientGroup.mk' (artinRaySubgroup m) γ) =
      finiteEtaleCoverAbsoluteAction W w γ := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    coverPresentation coverRatFuncAlgebra coverRatFuncTower coverFunctionField coverGalois m hm γ
  exact
    rfl

/-- The actual ray-quotient action reaches every deck transformation. -/
theorem finiteEtaleCoverRayAction_surjective :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    let coverPresentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra
      k U.functionField W.left.functionField
    let _ : Algebra (RatFunc k) W.left.functionField := coverPresentation.val
    let _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      coverPresentation.property.1
    let _ : FunctionField k W.left.functionField := coverPresentation.property.2
    have _ : _root_.IsGalois U.functionField W.left.functionField :=
      (show IsAbelianGalois U.functionField W.left.functionField from coverAbelian).toIsGalois
    ∀ (m : RayClass.Modulus k U.functionField)
    (hm : extensionConductor (k := k) (K := U.functionField)
      (L := W.left.functionField) ≤ m),
    Function.Surjective (finiteEtaleCoverRayAction W w k m hm) := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    coverPresentation coverRatFuncAlgebra coverRatFuncTower coverFunctionField coverGalois m hm τ
  obtain ⟨γ, hγ⟩ := finiteEtaleCoverAbsoluteAction_surjective W w τ
  exact ⟨QuotientGroup.mk' (artinRaySubgroup m) γ, hγ⟩

/-- The action of each actual restricted ray family is exactly its native
finite Artin value in the original deck group. -/
theorem finiteEtaleCoverRayAction_restrictedProduct :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra k W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap k U.functionField)).toAlgebra
    let _ : IsScalarTower k U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    let coverPresentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra
      k U.functionField W.left.functionField
    let _ : Algebra (RatFunc k) W.left.functionField := coverPresentation.val
    let _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      coverPresentation.property.1
    let _ : FunctionField k W.left.functionField := coverPresentation.property.2
    have _ : _root_.IsGalois U.functionField W.left.functionField :=
      (show IsAbelianGalois U.functionField W.left.functionField from coverAbelian).toIsGalois
    ∀ (m : RayClass.Modulus k U.functionField)
    (hm : extensionConductor (k := k) (K := U.functionField)
      (L := W.left.functionField) ≤ m) (a : RayRestrictedProduct m),
    finiteEtaleCoverRayAction W w k m hm (restrictedProductAbsoluteArtin m a) =
      (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
        (restrictedProductFiniteArtin m hm a) := by
  intro integralCover coverAlgebra finiteCover coverConstants coverConstantTower coverDivisors
    coverPresentation coverRatFuncAlgebra coverRatFuncTower coverFunctionField coverGalois m hm a
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  rw [restrictedProductAbsoluteArtin_idele, finiteEtaleCoverRayAction_mk,
    finiteEtaleCoverAbsoluteAction_artin, restrictedProductFiniteArtin_idele]
  rfl

end EtaleFundamentalGroups
