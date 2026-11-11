/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.EtaleFundamentalGroups.Inertia.OpenSourceBoundaryPlaces
public import Nyll.EtaleFundamentalGroups.Inertia.ActualWildResidualCore
public import Nyll.EtaleFundamentalGroups.Inertia.Tame.BoundaryWildAbelianKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayWildIntrinsic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.OriginalArithmeticDegree
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Ideal.Maximal
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinRamification
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinSeparation
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect

/-!
# The original boundary-wild abelian quotient is the actual reduced ray quotient

The native wild image at each actual closed point is determined by its
ordinary inertia image and the original residue characteristic. The
proved ordinary-inertia comparison therefore identifies it with the
depth-one local Artin image in the same original absolute abelian group.

The actual open-curve generic kernel supplies the depth-zero images at
the actual interior points. Together with the actual finite boundary
modulus, these equalities identify the independently defined original
boundary-wild abelian quotient with the actual global Artin ray quotient.
The construction retains the original Galois representatives and their
marked arithmetic Frobenius degree.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicCurve SchemeTheory LocalClassFieldTheory TopologicalSpace

namespace EtaleFundamentalGroups

attribute [local instance]
  Inertia.normalizationCommAlgGaloisAction
  Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring

namespace Inertia

section SuppliedSource

variable {k F : Type u} [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]
  (hp : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))

/-- The original wild inertia at an actual supplied-source normalization
prime has exactly the original principal-unit Artin image. The comparison
uses the proved ordinary inertia images and the common residue
characteristic, without choosing an identification of wild actions. -/
theorem closedPointSourceNormalizationWild_image (x : closedPoints X) :
    let A := X.presheaf.stalk x.val
    let Ω := SeparableClosure F
    let : IsDiscreteValuationRing A :=
      SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c x.val
        (mem_closedPoints_iff.mp x.property)
    let : Algebra A F := genericFieldSourceStalkAlgebra p x.val
    let : IsFractionRing A F := genericFieldSourceStalk_isFractionRing p x.val
    let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
    let : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq' rfl
    ∀ Q : MaximalSpectrum (normalizationCommAlgCat A Ω),
      let : Q.asIdeal.IsMaximal := Q.isMaximal
      (actualNormalizationWildSubgroup A F Ω Q.asIdeal).map
        ((ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/F)).comp
          (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom') =
        FunctionField.RayClass.placeArtinUnitImage (closedPointSourcePlace c p hp x) 1 := by
  intro A Ω instDVR instAF instFrac instAΩ instAFΩ Q instQ
  let v := closedPointSourcePlace c p hp x
  have hpchar : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  let : Algebra k A := NeronModelInfra.stalkAlgebra c x.val
  have : CharP (IsLocalRing.ResidueField A) (ringChar k) :=
    CharP.of_ringHom_of_ne_zero
      ((IsLocalRing.residue A).comp (algebraMap k A)) (ringChar k) hpchar.out.ne_zero
  let a := ProCGroups.Abelian.TopologicalAbelianization.mkₜ Gal(Ω/F)
  let f : (actualNormalizationInertiaGroup A F Ω Q.asIdeal).carrier →ₜ*
      TopologicalAbelianization Gal(Ω/F) :=
    { toMonoidHom := a.toMonoidHom.comp
        (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom'
      continuous_toFun := a.continuous_toFun.comp continuous_subtype_val }
  have hf : f.toMonoidHom.range = FunctionField.RayClass.placeArtinUnitImage v 0 := by
    have hrange : f.toMonoidHom.range =
        (Q.asIdeal.inertia Gal(Ω/F)).map a.toMonoidHom := by
      apply Subgroup.ext
      intro z
      constructor
      · rintro ⟨σ, hσ⟩
        exact ⟨σ.val, σ.property, hσ⟩
      · rintro ⟨σ, hσ, h⟩
        exact ⟨⟨σ, hσ⟩, h⟩
    exact hrange.trans (closedPointSourceNormalizationInertia_image c p hp x Q)
  have hcore := congrArg
    (fun I : Subgroup (TopologicalAbelianization Gal(Ω/F)) =>
      (ProCGroups.ProC.proCResidualCore
        (ProCGroups.FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ)) I).map I.subtype) hf
  exact (actualNormalizationWildSubgroup_map_eq_rangeResidualCore
    A F Ω Q.asIdeal (ringChar k) f).trans
      (hcore.trans (FunctionField.RayClass.placeArtinUnitImage_one_eq_residualCore v).symm)

end SuppliedSource

end Inertia

namespace Tame

attribute [local instance] integralOpenDominant Inertia.smoothOpenCurve

section SuppliedBoundary

variable {k F : Type u} [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ X) [IsOpenImmersion j]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (hp : (p ≫ j) ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))

/-- The actual absolute wild image used in the original boundary quotient
has the depth-one Artin image at its actual supplied-field place. Every
original normalization prime is included, and a maximal prime exists. -/
theorem absoluteNormalizationWildImageAt_map_localUnits (x : closedPoints X) :
    (absoluteNormalizationWildImageAt k F (SeparableClosure F) c j p x.val
      (mem_closedPoints_iff.mp x.property)).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk Gal(SeparableClosure F/F)) =
      FunctionField.RayClass.placeArtinUnitImage
        (Inertia.closedPointSourcePlace c (p ≫ j) hp x) 1 := by
  let A := X.presheaf.stalk x.val
  let Ω := SeparableClosure F
  have : IsDiscreteValuationRing A :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c x.val
      (mem_closedPoints_iff.mp x.property)
  let : Algebra A F := genericFieldSourceStalkAlgebra (p ≫ j) x.val
  have : IsFractionRing A F := genericFieldSourceStalk_isFractionRing (p ≫ j) x.val
  let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq' rfl
  have : Nontrivial (normalizationCommAlgCat A Ω) := by
    change Nontrivial (integralClosure A Ω)
    infer_instance
  obtain ⟨Q₀, hQ₀⟩ := Ideal.exists_maximal (normalizationCommAlgCat A Ω)
  have : Nonempty (MaximalSpectrum (normalizationCommAlgCat A Ω)) := ⟨⟨Q₀, hQ₀⟩⟩
  let I : MaximalSpectrum (normalizationCommAlgCat A Ω) → Subgroup Gal(Ω/F) := fun Q =>
    let : Q.asIdeal.IsMaximal := Q.isMaximal
    (Inertia.actualNormalizationWildSubgroup A F Ω Q.asIdeal).map
      (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom'
  let a := ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/F)
  change (iSup I).map a = _
  have hI (Q : MaximalSpectrum (normalizationCommAlgCat A Ω)) :
      (I Q).map a = FunctionField.RayClass.placeArtinUnitImage
        (Inertia.closedPointSourcePlace c (p ≫ j) hp x) 1 := by
    have : Q.asIdeal.IsMaximal := Q.isMaximal
    change ((Inertia.actualNormalizationWildSubgroup A F Ω Q.asIdeal).map
      (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom').map a = _
    exact (Subgroup.map_map (Inertia.actualNormalizationWildSubgroup A F Ω Q.asIdeal) a
      (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom').trans
        (Inertia.closedPointSourceNormalizationWild_image c (p ≫ j) hp x Q)
  exact (Subgroup.map_iSup a I).trans ((iSup_congr hI).trans iSup_const)

end SuppliedBoundary

private theorem closure_closure_sup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I W : Subgroup G) :
    (I.topologicalClosure ⊔ W).topologicalClosure = (I ⊔ W).topologicalClosure := by
  apply le_antisymm
  · apply Subgroup.topologicalClosure_minimal
    · apply sup_le
      · apply Subgroup.topologicalClosure_minimal
        · exact le_sup_left.trans (Subgroup.le_topologicalClosure (I ⊔ W))
        · exact Subgroup.isClosed_topologicalClosure (I ⊔ W)
      · exact le_sup_right.trans (Subgroup.le_topologicalClosure (I ⊔ W))
    · exact Subgroup.isClosed_topologicalClosure (I ⊔ W)
  · apply Subgroup.topologicalClosure_minimal
    · exact (sup_le_sup (Subgroup.le_topologicalClosure I) le_rfl).trans
        (Subgroup.le_topologicalClosure (I.topologicalClosure ⊔ W))
    · exact Subgroup.isClosed_topologicalClosure (I.topologicalClosure ⊔ W)

section GenericOpen

variable {k F : Type u} [Field k] [Finite k] [Field F] [Algebra k F]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] [IsProper c]
  (j : U ⟶ X) [IsOpenImmersion j]

variable (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (hp : p ≫ (j ≫ c) = Spec.map (CommRingCat.ofHom (algebraMap k F)))

variable [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]

local notation "Ω" => SeparableClosure F
local notation "G" => Gal(SeparableClosure F/F)
local notation "B" => BoundaryWildQuotient k F Ω c j p
local notation "m" => Inertia.genericSourceBoundaryModulus c j p hp
local notation "Ab" => ProCGroups.Abelian.TopologicalAbelianization.mk

/-- The native absolute boundary images are exactly the depth-one images
indexed by the actual closed boundary points of the proper model. -/
theorem absoluteGenericBoundaryWildImage_eq_localUnits :
    (⨆ (x : X) (hx : IsClosed ({x} : Set X)) (_ : x ∉ Set.range j),
      (absoluteNormalizationWildImageAt k F Ω c j p x hx).map (Ab G)) =
      ⨆ (x : closedPoints X) (_ : x.val ∉ Set.range j),
        FunctionField.RayClass.placeArtinUnitImage
          (Inertia.genericSourcePlaceEquiv c j p hp x) 1 := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro hboundary
    let x' : closedPoints X := ⟨x, mem_closedPoints_iff.mpr hx⟩
    have himage := absoluteNormalizationWildImageAt_map_localUnits c j p
      ((Category.assoc p j c).trans hp) x'
    change (absoluteNormalizationWildImageAt k F Ω c j p x hx).map (Ab G) =
      FunctionField.RayClass.placeArtinUnitImage (Inertia.genericSourcePlaceEquiv c j p hp x') 1
      at himage
    rw [himage]
    exact le_iSup_of_le x' (le_iSup_of_le hboundary le_rfl)
  · apply iSup_le
    intro x
    apply iSup_le
    intro hboundary
    have himage := absoluteNormalizationWildImageAt_map_localUnits c j p
      ((Category.assoc p j c).trans hp) x
    change (absoluteNormalizationWildImageAt k F Ω c j p x.val
      (mem_closedPoints_iff.mp x.property)).map (Ab G) =
      FunctionField.RayClass.placeArtinUnitImage (Inertia.genericSourcePlaceEquiv c j p hp x) 1
      at himage
    rw [← himage]
    exact le_iSup_of_le x.val
      (le_iSup_of_le (mem_closedPoints_iff.mp x.property) (le_iSup_of_le hboundary le_rfl))

variable [IsNormalIntegral U]

/-- The independently defined original boundary-wild abelian map has
exactly the actual reduced Artin ray subgroup as its kernel. -/
theorem genericBoundaryWildAbsoluteAbelianHom_ker_eq_artinRaySubgroup :
    (boundaryWildAbsoluteAbelianHom k F Ω c j p).toMonoidHom.ker =
      FunctionField.RayClass.artinRaySubgroup m := by
  rw [boundaryWildAbsoluteAbelianHom_ker,
    Inertia.fieldSourceAbsoluteGaloisHom_ker_localUnits (j ≫ c) p hp,
    absoluteGenericBoundaryWildImage_eq_localUnits c j p hp,
    Inertia.artinRaySubgroup_genericSourceBoundary c j p hp]
  exact closure_closure_sup _ _

/-- The actual original boundary-wild abelian fundamental group is
topologically isomorphic to the actual reduced global Artin ray quotient.
The isomorphism is obtained from the proved equality of actual kernels. -/
def genericBoundaryWildRayEquiv :
    TopologicalAbelianization B ≃ₜ*
      (localAbsoluteAbelianProfinite F ⧸ FunctionField.RayClass.artinRaySubgroup m) := by
  let N := FunctionField.RayClass.artinRaySubgroup m
  let f := boundaryWildAbsoluteAbelianHom k F Ω c j p
  have hker : f.toMonoidHom.ker = N :=
    genericBoundaryWildAbsoluteAbelianHom_ker_eq_artinRaySubgroup c j p hp
  let lift := ProCGroups.QuotientGroup.liftₜ N f hker.symm.le
  have hbij : Function.Bijective lift := by
    constructor
    · exact (QuotientGroup.injective_lift_iff N f.toMonoidHom hker.symm.le).mpr hker.symm
    · intro b
      obtain ⟨a, ha⟩ := boundaryWildAbsoluteAbelianHom_surjective k F Ω c j p b
      exact ⟨QuotientGroup.mk' N a, ha⟩
  exact (ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    lift.toMonoidHom lift.continuous_toFun hbij).symm

/-- On every original absolute abelian representative, the comparison is
the original ray quotient projection. -/
theorem genericBoundaryWildRayEquiv_absoluteAbelian (a : TopologicalAbelianization G) :
    genericBoundaryWildRayEquiv c j p hp (boundaryWildAbsoluteAbelianHom k F Ω c j p a) =
      QuotientGroup.mk' (FunctionField.RayClass.artinRaySubgroup m) a := by
  apply (genericBoundaryWildRayEquiv c j p hp).symm.injective
  rw [(genericBoundaryWildRayEquiv c j p hp).symm_apply_apply]
  rfl

/-- The original generic automorphism keeps its literal ray class under
the native boundary quotient comparison. -/
theorem genericBoundaryWildRayEquiv_absolute_mk (σ : G) :
    genericBoundaryWildRayEquiv c j p hp
      (Ab B (boundaryWildProjection k F Ω c j p
        (fieldSourceAbsoluteGaloisHom F Ω p σ))) =
      QuotientGroup.mk' (FunctionField.RayClass.artinRaySubgroup m) (Ab G σ) :=
  genericBoundaryWildRayEquiv_absoluteAbelian c j p hp (Ab G σ)

/-- The original continuous ray map on the original fundamental group,
constructed through the actual native boundary-wild quotient. -/
def genericBoundaryRayHom :
    π₁ᵉᵗ(ξ F Ω ≫ p) →ₜ*
      (localAbsoluteAbelianProfinite F ⧸ FunctionField.RayClass.artinRaySubgroup m) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (genericBoundaryWildRayEquiv c j p hp)).comp
    ((ProCGroups.Abelian.TopologicalAbelianization.mkₜ B).comp
      (boundaryWildProjection k F Ω c j p))

/-- The actual fundamental-group ray map retains each original generic
absolute Galois representative. -/
theorem genericBoundaryRayHom_fieldSource (σ : G) :
    genericBoundaryRayHom c j p hp (fieldSourceAbsoluteGaloisHom F Ω p σ) =
      QuotientGroup.mk' (FunctionField.RayClass.artinRaySubgroup m) (Ab G σ) :=
  genericBoundaryWildRayEquiv_absolute_mk c j p hp σ

section Arithmetic

variable [GeometricallyIntegral (j ≫ c)]

/-- The comparison preserves the original marked arithmetic Frobenius
degree for every original fundamental-group element. Geometric
integrality supplies the full-constants statement used in normalization. -/
theorem genericBoundaryWildRayEquiv_degree (γ : π₁ᵉᵗ(ξ F Ω ≫ p)) :
    let _ : Algebra k Ω := ((algebraMap F Ω).comp (algebraMap k F)).toAlgebra
    let _ : IsScalarTower k F Ω := IsScalarTower.of_algebraMap_eq' rfl
    FunctionField.RayClass.rayAbelianDegree m
      (genericBoundaryWildRayEquiv c j p hp (Ab B (boundaryWildProjection k F Ω c j p γ))) =
      originalArithmeticDegree k F Ω (j ≫ c) p γ := by
  intro constantClosureAlgebra constantClosureTower
  obtain ⟨σ, hσ⟩ := fieldSourceAbsoluteGaloisHom_surjective F Ω p γ
  rw [← hσ, genericBoundaryWildRayEquiv_absolute_mk c j p hp σ]
  exact FunctionField.RayClass.rayAbelianDegree_fieldSource_geometricallyIntegral
    k F (j ≫ c) p m hp σ

end Arithmetic

end GenericOpen

section CanonicalOpen

/-- The original generic-point source of an integral scheme is dominant. -/
theorem canonicalSourceDominant (U : Scheme.{u}) [IsIntegral U] :
    IsDominant (U.fromSpecStalk (genericPoint U)) := genericPoint_isDominant U

attribute [local instance] AlgebraicGeometry.FiniteEtale.genericPoint_isDominant

variable {k : Type u} [Field k] [Finite k]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] [IsProper c]
  (j : U ⟶ X) [IsOpenImmersion j]

local notation "F" => U.functionField
local notation "Ω" => SeparableClosure U.functionField
local notation "p" => U.fromSpecStalk (genericPoint U)
local notation "hp₀" => fromSpecStalk_genericPoint_comp_base (j ≫ c)
local notation "G" => Gal(SeparableClosure U.functionField/U.functionField)
local notation "B" => BoundaryWildQuotient k F Ω c j p
local notation "m" => Inertia.openSourceBoundaryModulus c j
local notation "Ab" => ProCGroups.Abelian.TopologicalAbelianization.mk

/-- The native absolute boundary images are exactly the depth-one images
indexed by the actual closed boundary points of the proper model. -/
theorem absoluteBoundaryWildImage_eq_localUnits :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F],
      (⨆ (x : X) (hx : IsClosed ({x} : Set X)) (_ : x ∉ Set.range j),
        (absoluteNormalizationWildImageAt k F Ω c j p x hx).map (Ab G)) =
        ⨆ (x : closedPoints X) (_ : x.val ∉ Set.range j),
          FunctionField.RayClass.placeArtinUnitImage (Inertia.openSourcePlaceEquiv c j x) 1 := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  exact absoluteGenericBoundaryWildImage_eq_localUnits c j p hp₀

variable [IsNormalIntegral U]

/-- The independently defined original boundary-wild abelian map has
exactly the actual reduced Artin ray subgroup as its kernel. -/
theorem boundaryWildAbsoluteAbelianHom_ker_eq_artinRaySubgroup :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F],
      (boundaryWildAbsoluteAbelianHom k F Ω c j p).toMonoidHom.ker =
        FunctionField.RayClass.artinRaySubgroup m := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  exact genericBoundaryWildAbsoluteAbelianHom_ker_eq_artinRaySubgroup c j p hp₀

/-- The actual original boundary-wild abelian fundamental group is
topologically isomorphic to the actual reduced global Artin ray quotient.
The isomorphism is obtained from the proved equality of actual kernels. -/
def boundaryWildRayEquiv :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F],
      TopologicalAbelianization B ≃ₜ*
        (localAbsoluteAbelianProfinite F ⧸ FunctionField.RayClass.artinRaySubgroup m) := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  exact genericBoundaryWildRayEquiv c j p hp₀

/-- On every original absolute abelian representative, the comparison is
the original ray quotient projection. -/
theorem boundaryWildRayEquiv_absoluteAbelian :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F]
      (a : TopologicalAbelianization G),
      boundaryWildRayEquiv c j (boundaryWildAbsoluteAbelianHom k F Ω c j p a) =
        QuotientGroup.mk' (FunctionField.RayClass.artinRaySubgroup m) a := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors a
  exact genericBoundaryWildRayEquiv_absoluteAbelian c j p hp₀ a

/-- The original generic automorphism keeps its literal ray class under
the native boundary quotient comparison. -/
theorem boundaryWildRayEquiv_absolute_mk :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F] (σ : G),
      boundaryWildRayEquiv c j
        (Ab B (boundaryWildProjection k F Ω c j p
          (fieldSourceAbsoluteGaloisHom F Ω p σ))) =
        QuotientGroup.mk' (FunctionField.RayClass.artinRaySubgroup m) (Ab G σ) := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors σ
  exact genericBoundaryWildRayEquiv_absolute_mk c j p hp₀ σ

/-- The original continuous ray map on the original fundamental group,
constructed through the actual native boundary-wild quotient. -/
def originalBoundaryRayHom :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F],
      π₁ᵉᵗ(ξ F Ω ≫ p) →ₜ*
        (localAbsoluteAbelianProfinite F ⧸ FunctionField.RayClass.artinRaySubgroup m) := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  exact genericBoundaryRayHom c j p hp₀

/-- The actual fundamental-group ray map retains each original generic
absolute Galois representative. -/
theorem originalBoundaryRayHom_fieldSource :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F] (σ : G),
      originalBoundaryRayHom c j (fieldSourceAbsoluteGaloisHom F Ω p σ) =
        QuotientGroup.mk' (FunctionField.RayClass.artinRaySubgroup m) (Ab G σ) := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors σ
  exact genericBoundaryRayHom_fieldSource c j p hp₀ σ

variable [GeometricallyIntegral (j ≫ c)]

/-- The comparison preserves the original marked arithmetic Frobenius
degree for every original fundamental-group element. Geometric
integrality supplies the full-constants statement used in normalization. -/
theorem boundaryWildRayEquiv_degree :
    let _ : Algebra k F := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F] [HasPrincipalDivisors k F],
    let _ : Algebra k Ω := ((algebraMap F Ω).comp (algebraMap k F)).toAlgebra
    let _ : IsScalarTower k F Ω := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (γ : π₁ᵉᵗ(ξ F Ω ≫ p)),
      FunctionField.RayClass.rayAbelianDegree m
        (boundaryWildRayEquiv c j (Ab B (boundaryWildProjection k F Ω c j p γ))) =
        originalArithmeticDegree k F Ω (j ≫ c) p γ := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
    constantClosureAlgebra constantClosureTower γ
  exact genericBoundaryWildRayEquiv_degree c j p hp₀ γ

end CanonicalOpen

end Tame

end EtaleFundamentalGroups
