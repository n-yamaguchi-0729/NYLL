/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationDiagram
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationNaturality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.LocalGeometricStalkChangeFieldIso
public import Nyll.EtaleFundamentalGroups.StrictHenselian.LocalGeometricStalkNaturality
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Whiskering

/-!
# Field changes in the actual family-specialization diagram

Extension of the generic pointing field uses the literal composite of the
chosen lift with the field embedding. Extension of the special pointing
field uses the proved inverse of the actual strict-local comparison.
Both constructions retain the original chosen lift. The corresponding
family arrows factor through the actual geometric-fiber and strict-local
family maps, and hence give comparisons of the actual finite étale
pullback functors.

These are geometric comparisons. They do not presuppose a proper
closed-fiber equivalence or define a family-specialization homomorphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X S : Scheme.{u}} (f : X ⟶ S)
  {Ωs Ωt Ωt' : Type u} [Field Ωs] [Field Ωt] [Field Ωt']
  (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
  (ψ : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
  (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ localGeometricStalkToScheme s = t)
  (κ : Ωt →+* Ωt')

include hψ in
/-- The literal generic-field extension of the original lift lies over
the literal extended generic point. -/
theorem localGeometricStalkLift_changeGenericField_toScheme :
    Spec.map (CommRingCat.ofHom (κ.comp ψ)) ≫ localGeometricStalkToScheme s =
      Spec.map (CommRingCat.ofHom κ) ≫ t := by
  change Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom κ) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, hψ]

/-- The original generic-family arrow after the actual field-change map
equals the arrow associated to the literal extended lift. -/
theorem familySpecializationGenericMap_changeGenericField :
    familyGeometricFiberMap f f (𝟙 X) (𝟙 S)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        (Spec.map (CommRingCat.ofHom κ) ≫ t) t κ (Category.comp_id _) ≫
      familySpecializationGenericMap f s t ψ hψ =
    familySpecializationGenericMap f s (Spec.map (CommRingCat.ofHom κ) ≫ t)
      (κ.comp ψ) (localGeometricStalkLift_changeGenericField_toScheme s t ψ hψ κ) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familySpecializationGenericMap_fst,
      familyGeometricFiberMap_fst_assoc]
    exact congrArg (fun q => pullback.fst (Spec.map (CommRingCat.ofHom κ) ≫ t) f ≫ q)
      (Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom κ)).symm
  · simp only [Category.assoc, familySpecializationGenericMap_snd,
      familyGeometricFiberMap_snd, Category.comp_id]

/-- Actual finite étale pullbacks compare along the extended generic lift
and the original geometric-fiber field-change map. -/
def familySpecializationGenericFieldPullbackComp :
    FiniteEtale.pullback
        (familySpecializationGenericMap f s (Spec.map (CommRingCat.ofHom κ) ≫ t)
          (κ.comp ψ) (localGeometricStalkLift_changeGenericField_toScheme s t ψ hψ κ)) ≅
      FiniteEtale.pullback (familySpecializationGenericMap f s t ψ hψ) ⋙
        FiniteEtale.pullback (familyGeometricFiberMap f f (𝟙 X) (𝟙 S)
          ((Category.comp_id f).trans (Category.id_comp f).symm)
          (Spec.map (CommRingCat.ofHom κ) ≫ t) t κ (Category.comp_id _)) :=
  MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (familyGeometricFiberMap f f (𝟙 X) (𝟙 S)
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      (Spec.map (CommRingCat.ofHom κ) ≫ t) t κ (Category.comp_id _))
    (familySpecializationGenericMap f s t ψ hψ)
    (familySpecializationGenericMap f s (Spec.map (CommRingCat.ofHom κ) ≫ t)
      (κ.comp ψ) (localGeometricStalkLift_changeGenericField_toScheme s t ψ hψ κ))
    (familySpecializationGenericMap_changeGenericField f s t ψ hψ κ).symm

/-- The generic-field comparison retains the canonical comparison at each
point of the actual extended generic fiber. -/
theorem familySpecializationGenericFieldPullbackComp_fiber
    {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom κ) ≫ t) f) :
    let a := familyGeometricFiberMap f f (𝟙 X) (𝟙 S)
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      (Spec.map (CommRingCat.ofHom κ) ≫ t) t κ (Category.comp_id _)
    let b := familySpecializationGenericMap f s t ψ hψ
    let c := familySpecializationGenericMap f s (Spec.map (CommRingCat.ofHom κ) ≫ t)
      (κ.comp ψ) (localGeometricStalkLift_changeGenericField_toScheme s t ψ hψ κ)
    let hc : a ≫ b = c := familySpecializationGenericMap_changeGenericField f s t ψ hψ κ
    Functor.isoWhiskerRight (familySpecializationGenericFieldPullbackComp f s t ψ hψ κ)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.associator (FiniteEtale.pullback b) (FiniteEtale.pullback a)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback b) (FiniteEtale.pullbackFiberIso a ξ) ≪≫
      FiniteEtale.pullbackFiberIso b (ξ ≫ a) ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc ξ a b).trans (congrArg (fun q => ξ ≫ q) hc))) =
      FiniteEtale.pullbackFiberIso c ξ := by
  exact FiniteEtale.pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso _ _ _
    (familySpecializationGenericMap_changeGenericField f s t ψ hψ κ).symm ξ
    ((Category.assoc _ _ _).trans
      (congrArg (fun q => ξ ≫ q)
        (familySpecializationGenericMap_changeGenericField f s t ψ hψ κ)))

section Special

variable [IsSepClosed Ωs] {Ωs' : Type u} [Field Ωs'] (ι : Ωs →+* Ωs')

/-- Changing the special pointing field gives an isomorphism of the
actual families over the two strict-local models. -/
theorem familyStrictLocalMap_changeField_isIso :
    IsIso (familyStrictLocalMap f f (𝟙 X) (𝟙 S)
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)) := by
  have := localGeometricStalkMap_changeField_isIso s ι
  unfold familyStrictLocalMap
  infer_instance

/-- The constructed special-field lift recovers the original family
arrow through the actual isomorphism of strict-local families. -/
theorem familySpecializationGenericMap_changeSpecialField :
    familySpecializationGenericMap f (Spec.map (CommRingCat.ofHom ι) ≫ s) t
        (localGeometricStalkChangeFieldLift s ι ψ)
        (localGeometricStalkChangeFieldLift_toScheme s ι t ψ hψ) ≫
      familyStrictLocalMap f f (𝟙 X) (𝟙 S)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _) =
      familySpecializationGenericMap f s t ψ hψ := by
  let M := localGeometricStalkMap (𝟙 S)
    (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)
  have he : M ≫ CommRingCat.ofHom (localGeometricStalkChangeFieldLift s ι ψ) =
      CommRingCat.ofHom ψ :=
    congrArg CommRingCat.ofHom (localGeometricStalkChangeFieldLift_comp s ι ψ)
  have hSpec :
      Spec.map (CommRingCat.ofHom (localGeometricStalkChangeFieldLift s ι ψ)) ≫
        Spec.map M = Spec.map (CommRingCat.ofHom ψ) :=
    (Spec.map_comp M (CommRingCat.ofHom (localGeometricStalkChangeFieldLift s ι ψ))).symm.trans
      (congrArg Spec.map he)
  apply pullback.hom_ext
  · simp only [Category.assoc, familyStrictLocalMap_fst,
      familySpecializationGenericMap_fst_assoc, familySpecializationGenericMap_fst]
    exact congrArg (fun q => pullback.fst t f ≫ q) hSpec
  · simp only [Category.assoc, familyStrictLocalMap_snd,
      familySpecializationGenericMap_snd, Category.comp_id]

/-- The original pullback is compared with the pullback along the
constructed lift and the actual special-field model isomorphism. -/
def familySpecializationSpecialFieldPullbackComp :
    FiniteEtale.pullback (familySpecializationGenericMap f s t ψ hψ) ≅
      FiniteEtale.pullback (familyStrictLocalMap f f (𝟙 X) (𝟙 S)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)) ⋙
      FiniteEtale.pullback
        (familySpecializationGenericMap f (Spec.map (CommRingCat.ofHom ι) ≫ s) t
          (localGeometricStalkChangeFieldLift s ι ψ)
          (localGeometricStalkChangeFieldLift_toScheme s ι t ψ hψ)) :=
  MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (familySpecializationGenericMap f (Spec.map (CommRingCat.ofHom ι) ≫ s) t
      (localGeometricStalkChangeFieldLift s ι ψ)
      (localGeometricStalkChangeFieldLift_toScheme s ι t ψ hψ))
    (familyStrictLocalMap f f (𝟙 X) (𝟙 S)
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _))
    (familySpecializationGenericMap f s t ψ hψ)
    (familySpecializationGenericMap_changeSpecialField f s t ψ hψ ι).symm

/-- The special-field comparison agrees with the original canonical
fiber comparison at every point of the same original generic fiber. -/
theorem familySpecializationSpecialFieldPullbackComp_fiber
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ pullback t f) :
    let a := familySpecializationGenericMap f (Spec.map (CommRingCat.ofHom ι) ≫ s) t
      (localGeometricStalkChangeFieldLift s ι ψ)
      (localGeometricStalkChangeFieldLift_toScheme s ι t ψ hψ)
    let b := familyStrictLocalMap f f (𝟙 X) (𝟙 S)
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)
    let c := familySpecializationGenericMap f s t ψ hψ
    let hc : a ≫ b = c := familySpecializationGenericMap_changeSpecialField f s t ψ hψ ι
    Functor.isoWhiskerRight (familySpecializationSpecialFieldPullbackComp f s t ψ hψ ι)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.associator (FiniteEtale.pullback b) (FiniteEtale.pullback a)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback b) (FiniteEtale.pullbackFiberIso a ξ) ≪≫
      FiniteEtale.pullbackFiberIso b (ξ ≫ a) ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc ξ a b).trans (congrArg (fun q => ξ ≫ q) hc))) =
      FiniteEtale.pullbackFiberIso c ξ := by
  exact FiniteEtale.pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso _ _ _
    (familySpecializationGenericMap_changeSpecialField f s t ψ hψ ι).symm ξ
    ((Category.assoc _ _ _).trans
      (congrArg (fun q => ξ ≫ q)
        (familySpecializationGenericMap_changeSpecialField f s t ψ hψ ι)))

end Special

end EtaleFundamentalGroups.StrictHenselian
