/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationDiagram
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSchemeMap
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Whiskering

/-!
# Composition of the actual family-specialization diagrams

The existing strict-local composition theorem specifies the composite
field-valued lift as the second lift composed with the first canonical
strict-local map. Here this same lift is retained in the original family.
The actual generic-fiber arrows and the maps between strict-local families
compose, and their finite étale pullback comparisons agree with the
canonical comparison at every specified generic-fiber point.

This supplies the geometric and fiber-functor diagram for Stacks Project,
Lemma 58.16.2, https://stacks.math.columbia.edu/tag/0BUP. The inverse
proper closed-fiber equivalences and the resulting fundamental-group
specialization are not inputs or conclusions of these diagram results.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X S : Scheme.{u}} (f : X ⟶ S)
  {Ωs Ωt Ωv : Type u} [Field Ωs] [Field Ωt] [Field Ωv] [IsSepClosed Ωs]
  (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S) (v : Spec (.of Ωv) ⟶ S)
  (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
  (ψ : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
  (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
    (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom)
  (χ : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) →+* Ωv)
  (hχ : Spec.map (CommRingCat.ofHom χ) ≫ localGeometricStalkToScheme t = v)

include hχ in
/-- The literal composite lift used by strict-local composition retains the
original generic geometric point over the original base scheme. -/
theorem localGeometricStalkSpecializationLift_comp_toScheme :
    Spec.map (CommRingCat.ofHom
        (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)) ≫
      localGeometricStalkToScheme s = v := by
  let M := localGeometricStalkSpecializationMap s t h ψ hψ
  change Spec.map (M ≫ CommRingCat.ofHom χ) ≫ localGeometricStalkToScheme s = v
  exact
    (congrArg (fun q => q ≫ localGeometricStalkToScheme s)
      (Spec.map_comp M (CommRingCat.ofHom χ))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => Spec.map (CommRingCat.ofHom χ) ≫ q)
        (localGeometricStalkSpecializationMap_toScheme s t h ψ hψ)).trans hχ))

/-- Composing the second generic-fiber arrow with the first strict-local
family map is the generic-fiber arrow for the original composite lift. -/
theorem familySpecializationGenericMap_comp :
    familySpecializationGenericMap f t v χ hχ ≫
        familySpecializationModelMap f s t ψ h hψ =
      familySpecializationGenericMap f s v
        (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
        (localGeometricStalkSpecializationLift_comp_toScheme s t v h ψ hψ χ hχ) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familySpecializationModelMap_fst,
      familySpecializationGenericMap_fst_assoc, familySpecializationGenericMap_fst]
    exact congrArg (fun q => pullback.fst v f ≫ q)
      (Spec.map_comp (localGeometricStalkSpecializationMap s t h ψ hψ)
        (CommRingCat.ofHom χ)).symm
  · simp only [Category.assoc, familySpecializationModelMap_snd,
      familySpecializationGenericMap_snd]

/-- The pullback along the composite generic-fiber arrow is compared with
the successive actual pullbacks, retaining the original composite lift. -/
def familySpecializationGenericPullbackComp :
    FiniteEtale.pullback
        (familySpecializationGenericMap f s v
          (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
          (localGeometricStalkSpecializationLift_comp_toScheme s t v h ψ hψ χ hχ)) ≅
      FiniteEtale.pullback (familySpecializationModelMap f s t ψ h hψ) ⋙
        FiniteEtale.pullback (familySpecializationGenericMap f t v χ hχ) :=
  MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (familySpecializationGenericMap f t v χ hχ)
    (familySpecializationModelMap f s t ψ h hψ)
    (familySpecializationGenericMap f s v
      (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
      (localGeometricStalkSpecializationLift_comp_toScheme s t v h ψ hψ χ hχ))
    (familySpecializationGenericMap_comp f s t v h ψ hψ χ hχ).symm

/-- At every point of the original generic fiber, successive canonical
fiber comparisons agree with the canonical comparison for the literal
composite-lift arrow. -/
theorem familySpecializationGenericPullbackComp_fiber
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ pullback v f) :
    let i := familySpecializationGenericMap f t v χ hχ
    let j := familySpecializationModelMap f s t ψ h hψ
    let m := familySpecializationGenericMap f s v
      (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
      (localGeometricStalkSpecializationLift_comp_toScheme s t v h ψ hψ χ hχ)
    let hm : i ≫ j = m := familySpecializationGenericMap_comp f s t v h ψ hψ χ hχ
    Functor.isoWhiskerRight
        (familySpecializationGenericPullbackComp f s t v h ψ hψ χ hχ)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.associator (FiniteEtale.pullback j) (FiniteEtale.pullback i)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback j) (FiniteEtale.pullbackFiberIso i ξ) ≪≫
      FiniteEtale.pullbackFiberIso j (ξ ≫ i) ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc ξ i j).trans (congrArg (fun q => ξ ≫ q) hm))) =
      FiniteEtale.pullbackFiberIso m ξ := by
  exact FiniteEtale.pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso
    (familySpecializationGenericMap f t v χ hχ)
    (familySpecializationModelMap f s t ψ h hψ)
    (familySpecializationGenericMap f s v
      (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
      (localGeometricStalkSpecializationLift_comp_toScheme s t v h ψ hψ χ hχ))
    (familySpecializationGenericMap_comp f s t v h ψ hψ χ hχ).symm ξ
    ((Category.assoc ξ (familySpecializationGenericMap f t v χ hχ)
        (familySpecializationModelMap f s t ψ h hψ)).trans
      (congrArg (fun q => ξ ≫ q)
        (familySpecializationGenericMap_comp f s t v h ψ hψ χ hχ)))

variable [IsSepClosed Ωt]
  (k : v (closedPoint Ωv) ⤳ t (closedPoint Ωt))
  (hχring : χ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo t).hom) =
    (Scheme.stalkSpecializationToField (t (closedPoint Ωt)) v k).hom)

/-- The two actual strict-local family maps compose to the one associated
to the original composite lift and the composite specialization. -/
theorem familySpecializationModelMap_comp :
    familySpecializationModelMap f t v χ k hχring ≫
        familySpecializationModelMap f s t ψ h hψ =
      familySpecializationModelMap f s v
        (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
        (k.trans h)
        (localGeometricStalkSpecializationLift_comp_structure
          s t v h k ψ hψ χ hχring) := by
  have hmaps :
      Spec.map (localGeometricStalkSpecializationMap t v k χ hχring) ≫
          Spec.map (localGeometricStalkSpecializationMap s t h ψ hψ) =
        Spec.map (localGeometricStalkSpecializationMap s v (k.trans h)
          (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
          (localGeometricStalkSpecializationLift_comp_structure s t v h k ψ hψ χ hχring)) :=
    (Spec.map_comp (localGeometricStalkSpecializationMap s t h ψ hψ)
      (localGeometricStalkSpecializationMap t v k χ hχring)).symm.trans
      (congrArg Spec.map
        (localGeometricStalkSpecializationMap_comp s t v h k ψ hψ χ hχring))
  apply pullback.hom_ext
  · simp only [Category.assoc, familySpecializationModelMap_fst,
      familySpecializationModelMap_fst_assoc]
    exact congrArg (fun q => pullback.fst (localGeometricStalkToScheme v) f ≫ q) hmaps
  · simp only [Category.assoc, familySpecializationModelMap_snd]

/-- The comparison of the actual three-point strict-local family
pullbacks uses the composite map proved from the original chosen lifts. -/
def familySpecializationModelPullbackComp :
    FiniteEtale.pullback
        (familySpecializationModelMap f s v
          (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
          (k.trans h)
          (localGeometricStalkSpecializationLift_comp_structure s t v h k ψ hψ χ hχring)) ≅
      FiniteEtale.pullback (familySpecializationModelMap f s t ψ h hψ) ⋙
        FiniteEtale.pullback (familySpecializationModelMap f t v χ k hχring) :=
  MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (familySpecializationModelMap f t v χ k hχring)
    (familySpecializationModelMap f s t ψ h hψ)
    (familySpecializationModelMap f s v
      (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
      (k.trans h)
      (localGeometricStalkSpecializationLift_comp_structure s t v h k ψ hψ χ hχring))
    (familySpecializationModelMap_comp f s t v h ψ hψ χ k hχring).symm

end EtaleFundamentalGroups.StrictHenselian
