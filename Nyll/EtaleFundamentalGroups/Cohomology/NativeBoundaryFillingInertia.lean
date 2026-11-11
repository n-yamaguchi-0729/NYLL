/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.BoundaryStrictGenericPointComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.GeometricSourceAbelianImage
public import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkGaloisRestriction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality

/-!
# Filling a boundary component kills the original normalization inertia

The strict-local source at the original normalization prime is identified
with the standard boundary source over the actual open curve. Its Galois
restriction image is the original inertia subgroup. The resulting kernel
formula retains the given generic morphism and its actual absolute-Galois
map, and includes the entire wild inertia subgroup.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open ProCGroups.Abelian Yamaguchi26SolvableCoverings
open EtaleFundamentalGroups.StrictHenselian EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.Cohomology

universe u

private theorem fieldSource_restriction_point_square
    (F E Ω : Type u) [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
    [IsSepClosure F Ω] [IsSepClosure E Ω] [IsSepClosed Ω]
    {U : Scheme.{u}} [IsIntegral U]
    (p : Spec (.of F) ⟶ U) (r : Spec (.of E) ⟶ U)
    (hpoint : ξ E Ω ≫ r = ξ F Ω ≫ p) (σ : Gal(Ω/E)) :
    continuousConjAut (eqToIso (congrArg fiber hpoint))
        (fieldSourceAbsoluteGaloisHom E Ω r σ) =
      fieldSourceAbsoluteGaloisHom F Ω p (σ.restrictScalars F) := by
  have hE := fundamentalGroupHom_point_of_point_action r (ξ E Ω)
    (suppliedGaloisEquivFundamentalGroup E Ω σ) σ.toRingHom
    (suppliedGaloisEquivFundamentalGroup_point E Ω σ)
  have hF := fundamentalGroupHom_point_of_point_action p (ξ F Ω)
    (suppliedGaloisEquivFundamentalGroup F Ω (σ.restrictScalars F))
    (σ.restrictScalars F).toRingHom
    (suppliedGaloisEquivFundamentalGroup_point F Ω (σ.restrictScalars F))
  apply Aut.ext
  ext W w
  apply (fiberObjEquivHom (ξ F Ω ≫ p) W).injective
  apply Over.OverMorphism.ext
  exact (point_action_of_eqToIso hpoint _ σ.toRingHom hE W w).trans (hF W w).symm

private theorem geometricSourceAbelianHom_range_fieldTower
    (F E Ω : Type u) [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
    [IsSepClosure F Ω] [IsSepClosure E Ω] [IsSepClosed Ω]
    {U : Scheme.{u}} [IsIntegral U]
    (p : Spec (.of F) ⟶ U) (r : Spec (.of E) ⟶ U)
    (hpoint : ξ E Ω ≫ r = ξ F Ω ≫ p) :
    (geometricSourceAbelianHom r (ξ E Ω) (ξ F Ω ≫ p)
        (eqToIso (congrArg fiber hpoint))).toMonoidHom.range =
      (AlgEquiv.restrictScalarsHom F : Gal(Ω/E) →* Gal(Ω/F)).range.map
        ((TopologicalAbelianization.mk π₁ᵉᵗ(ξ F Ω ≫ p)).comp
          (fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom) := by
  let c := suppliedGaloisEquivFundamentalGroup E Ω
  let a := geometricSourceAbelianHom r (ξ E Ω) (ξ F Ω ≫ p)
    (eqToIso (congrArg fiber hpoint))
  let q := (TopologicalAbelianization.mk π₁ᵉᵗ(ξ F Ω ≫ p)).comp
    (fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom
  have hvalue (σ : Gal(Ω/E)) : a (c σ) = q (σ.restrictScalars F) :=
    congrArg (TopologicalAbelianization.mk π₁ᵉᵗ(ξ F Ω ≫ p))
      (fieldSource_restriction_point_square F E Ω p r hpoint σ)
  apply Subgroup.ext
  intro z
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨σ, rfl⟩ := c.surjective g
    exact ⟨σ.restrictScalars F, ⟨σ, rfl⟩, (hvalue σ).symm⟩
  · rintro ⟨σ, ⟨τ, rfl⟩, rfl⟩
    exact ⟨c τ, hvalue τ⟩

attribute [local instance] normalizationInertiaImageAction

/-- For one regular boundary component, the full abelian filling kernel is
the image of the original inertia at any maximal normalization prime of its
actual local ring. The displayed map is the original generic Galois map. -/
theorem boundaryFillingAbelianization_ker_eq_normalizationInertia
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [Subsingleton (Component D)] [IsIntegral (D.1.supportComplement : Scheme)]
    (E₀ : Component D) (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    [Algebra (X.presheaf.stalk (componentPoint D E₀)) K]
    [IsFractionRing (X.presheaf.stalk (componentPoint D E₀)) K]
    [Algebra (X.presheaf.stalk (componentPoint D E₀)) Ω]
    [IsScalarTower (X.presheaf.stalk (componentPoint D E₀)) K Ω]
    (p : Spec (.of K) ⟶ D.1.supportComplement)
    (hp : p ≫ D.1.supportComplement.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (componentPoint D E₀)) K)) ≫
        X.fromSpecStalk (componentPoint D E₀))
    (Q : Ideal (integralClosure (X.presheaf.stalk (componentPoint D E₀)) Ω)) [Q.IsMaximal] :
    (TopologicalAbelianization.map
        (fundamentalGroupHom D.1.supportComplement.ι (ξ K Ω ≫ p))).toMonoidHom.ker =
      (Q.inertia Gal(Ω/K)).map
        ((TopologicalAbelianization.mk π₁ᵉᵗ(ξ K Ω ≫ p)).comp
          (fieldSourceAbsoluteGaloisHom K Ω p).toMonoidHom) := by
  let x := componentPoint D E₀
  let A := X.presheaf.stalk x
  have : IsIntegrallyClosed A := IsNormalIntegral.stalk_isIntegrallyClosed x
  have : Algebra.IsAlgebraic A Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := Ω)).mpr inferInstance
  have : FaithfulSMul A Ω :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := Ω)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K Ω)
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A Ω Q).1
  have : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A Ω Q).2
  let ψ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
    (integralClosurePrimeBaseMap A Ω Q)
  have : IsLocalHom ψ := normalizationResiduePoint_isLocalHom A Ω Q
  let S := geometricStalk (Spec.map (CommRingCat.ofHom ψ))
  let E := FractionRing S
  let : Algebra K E := (normalizationStalkFractionBaseMap A K Ω Q).toAlgebra
  let : Algebra E Ω := (geometricStalkFractionToNormalizationField A Ω Q).toAlgebra
  have : IsScalarTower K E Ω := normalizationStalkFractionField_isScalarTower A K Ω Q
  have : IsSepClosure E Ω := normalizationStalkFractionField_isSepClosure A K Ω Q
  let r : Spec (.of E) ⟶ D.1.supportComplement := geometricStalkFractionFieldToComplement D x ψ
  have hcoeff : (algebraMap K E).comp (algebraMap A K) =
      (algebraMap S E).comp (geometricStalkStructureMap ψ) := by
    apply RingHom.ext
    intro a
    exact normalizationStalkFractionBaseMap_algebraMap A K Ω Q a
  have hr : ξ K E ≫ p = r := by
    apply (cancel_mono D.1.supportComplement.ι).mp
    rw [Category.assoc, hp]
    change Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ X.fromSpecStalk x) =
      r ≫ D.1.supportComplement.ι
    have hspec : Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A K)) =
      Spec.map (CommRingCat.ofHom ((algebraMap S E).comp (geometricStalkStructureMap ψ))) :=
      (Spec.map_comp (CommRingCat.ofHom (algebraMap A K))
        (CommRingCat.ofHom (algebraMap K E))).symm.trans
          (congrArg (fun f : A →+* E => Spec.map (CommRingCat.ofHom f)) hcoeff)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ X.fromSpecStalk x) hspec).trans
        (geometricStalkFractionFieldToComplement_comp_ι D x ψ).symm)
  have hpoint : ξ E Ω ≫ r = ξ K Ω ≫ p :=
    (congrArg (fun f => ξ E Ω ≫ f) hr.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ p) (fieldGeometricPoint_comp K E Ω)))
  let tQ := eqToIso (congrArg fiber hpoint)
  have hnative := geometricSourceAbelianHom_range_fieldTower K E Ω p r hpoint
  have hrestriction : (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range =
      Q.inertia Gal(Ω/K) := geometricStalkAbsoluteGalois_restriction_range A K Ω Q
  have : IsDiscreteValuationRing A := isDiscreteValuationRing_stalk_componentPoint D hreg E₀
  let : Field (boundaryStrictFractionField D E₀) := boundaryStrictFractionFieldField D hreg E₀
  obtain ⟨e, he⟩ := exists_boundaryStrictGenericMorphism_iso D hreg E₀ ψ
  obtain ⟨t⟩ := nonempty_fiber_iso
    (boundaryStrictGenericPoint D hreg E₀ ≫ boundaryStrictGenericMorphism D hreg E₀)
    (ξ K Ω ≫ p)
  have hsource := geometricSourceAbelianHom_range_eq_of_iso
    (boundaryStrictGenericMorphism D hreg E₀) r e he
    (boundaryStrictGenericPoint D hreg E₀) (ξ E Ω) (ξ K Ω ≫ p) t tQ
  calc
    _ = (strictBoundaryAbelianizationHom D hreg (ξ K Ω ≫ p) E₀ t).toMonoidHom.range :=
      boundaryFillingAbelianization_ker D hreg (ξ K Ω ≫ p) E₀ t
    _ = (geometricSourceAbelianHom r (ξ E Ω) (ξ K Ω ≫ p) tQ).toMonoidHom.range :=
      hsource.symm
    _ = (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range.map
        ((TopologicalAbelianization.mk π₁ᵉᵗ(ξ K Ω ≫ p)).comp
          (fieldSourceAbsoluteGaloisHom K Ω p).toMonoidHom) := hnative
    _ = _ := congrArg (Subgroup.map
      ((TopologicalAbelianization.mk π₁ᵉᵗ(ξ K Ω ≫ p)).comp
        (fieldSourceAbsoluteGaloisHom K Ω p).toMonoidHom)) hrestriction

end EtaleFundamentalGroups.Cohomology
