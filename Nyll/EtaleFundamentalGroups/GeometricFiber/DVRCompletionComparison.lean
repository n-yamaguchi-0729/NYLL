/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationResidueField
public import Nyll.ValuedFieldTheory.Valuation.Completion.DVRAdicCompletionIsDomainDVRIsAdicComplete
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Henselian

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilyGeometricFiberCartesian
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteGeometricSpecialization
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent

/-!
# The actual completion of a strict henselian DVR family

Completion preserves the residue field. Its fraction field and the original
geometric generic field embed into one algebraically closed field, compatibly
with their original embeddings of the fraction field of the DVR.
The completed proper family has Cartesian generic and closed fiber
comparisons preserving the maps to the original total space. The existing
complete-local comparison supplies its closed-fiber equivalence.
-/

@[expose] public section

noncomputable section

open IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]

/-- The canonical residue-field map of the actual completion is an isomorphism. -/
def dvrCompletionResidueEquiv :
    ResidueField D ≃+* ResidueField (AdicCompletion (maximalIdeal D) D) :=
  RingEquiv.ofBijective
    (ResidueField.map (algebraMap D (AdicCompletion (maximalIdeal D) D)))
    (AdicCompletion.residueField_map_bijective D)

theorem dvrCompletionResidueEquiv_residue (d : D) :
    dvrCompletionResidueEquiv D (residue D d) =
      residue (AdicCompletion (maximalIdeal D) D)
        (algebraMap D (AdicCompletion (maximalIdeal D) D) d) :=
  ResidueField.map_residue _ d

/-- The residue field of the completion is separably closed whenever that
of the original DVR is separably closed. -/
theorem dvrCompletion_residue_isSepClosed [IsSepClosed (ResidueField D)] :
    IsSepClosed (ResidueField (AdicCompletion (maximalIdeal D) D)) := by
  let e := dvrCompletionResidueEquiv D
  refine ⟨fun p hp => ?_⟩
  have h := (IsSepClosed.splits_of_separable (p.map e.symm.toRingHom)
    (hp.map)).map e.toRingHom
  simpa only [Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom,
    Polynomial.map_id] using h

/-- The completion map of a DVR is injective. -/
theorem dvrCompletionMap_injective :
    Function.Injective (algebraMap D (AdicCompletion (maximalIdeal D) D)) := by
  intro a b hab
  apply AdicCompletion.of_injective (maximalIdeal D) D
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply] using hab

variable [IsDomain (AdicCompletion (maximalIdeal D) D)]

/-- The actual fraction-field embedding induced by completion. -/
def dvrCompletionFractionMap :
    FractionRing D →+* FractionRing (AdicCompletion (maximalIdeal D) D) :=
  IsFractionRing.lift
    (g := (algebraMap (AdicCompletion (maximalIdeal D) D)
      (FractionRing (AdicCompletion (maximalIdeal D) D))).comp
        (algebraMap D (AdicCompletion (maximalIdeal D) D)))
    ((IsFractionRing.injective (AdicCompletion (maximalIdeal D) D)
      (FractionRing (AdicCompletion (maximalIdeal D) D))).comp
        (dvrCompletionMap_injective D))

theorem dvrCompletionFractionMap_algebraMap (d : D) :
    dvrCompletionFractionMap D (algebraMap D (FractionRing D) d) =
      algebraMap (AdicCompletion (maximalIdeal D) D)
        (FractionRing (AdicCompletion (maximalIdeal D) D))
          (algebraMap D (AdicCompletion (maximalIdeal D) D) d) :=
  IsFractionRing.lift_algebraMap _ d

omit [IsDomain (AdicCompletion (maximalIdeal D) D)] in
/-- An actual complete strictly henselian DVR and a common geometric
generic field, retaining the original generic embedding on every DVR element. -/
theorem exists_dvrCompletionFieldComparison
    [IsSepClosed (ResidueField D)]
    {K : Type u} [Field K] (η : FractionRing D →+* K) :
    ∃ (_ : IsDomain (AdicCompletion (maximalIdeal D) D))
      (_ : IsDiscreteValuationRing (AdicCompletion (maximalIdeal D) D))
      (_ : HenselianLocalRing (AdicCompletion (maximalIdeal D) D)),
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal D) D))
          (AdicCompletion (maximalIdeal D) D) ∧
      IsSepClosed (ResidueField (AdicCompletion (maximalIdeal D) D)) ∧
      ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
        (i : K →+* Ω)
        (η' : FractionRing (AdicCompletion (maximalIdeal D) D) →+* Ω),
        η'.comp (dvrCompletionFractionMap D) = i.comp η ∧
        (η'.comp (algebraMap (AdicCompletion (maximalIdeal D) D)
            (FractionRing (AdicCompletion (maximalIdeal D) D)))).comp
            (algebraMap D (AdicCompletion (maximalIdeal D) D)) =
          i.comp (η.comp (algebraMap D (FractionRing D))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨hC, hCDVR, hComplete, _, _, _⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
      D ϖ hϖ
  have hHenselian : HenselianLocalRing (AdicCompletion (maximalIdeal D) D) :=
    EtaleFundamentalGroups.henselianLocalRing_of_finiteEtale_local_of_isAdicComplete
      (R := AdicCompletion (maximalIdeal D) D)
      (S := AdicCompletion (maximalIdeal D) D)
  obtain ⟨Ω, hΩ, hΩclosed, i, η', hfield⟩ :=
    exists_algebraicallyClosedFieldSquare η (dvrCompletionFractionMap D)
  refine ⟨hC, hCDVR, hHenselian, hComplete, dvrCompletion_residue_isSepClosed D,
    Ω, hΩ, hΩclosed, i, η', hfield.symm, ?_⟩
  apply RingHom.ext
  intro d
  have h := RingHom.congr_fun hfield (algebraMap D (FractionRing D) d)
  simpa only [RingHom.comp_apply, dvrCompletionFractionMap_algebraMap] using h.symm

end EtaleFundamentalGroups.StrictHenselian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Complete the concrete DVR family and compare its actual fibers with
the existing DVR fibers, retaining their maps to the original `X`. -/
theorem exists_dvrCompletionFamilyComparison
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsSepClosed (ResidueField D)]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (p : Spec (.of D) ⟶ S)
    {K k : Type u} [Field K] [IsSepClosed K] [Field k] [IsSepClosed k]
    (η : FractionRing D →+* K) (o : ResidueField D →+* k) :
    let C := AdicCompletion (maximalIdeal D) D
    ∃ (_ : IsDomain C) (_ : IsDiscreteValuationRing C) (_ : HenselianLocalRing C),
      IsAdicComplete (maximalIdeal C) C ∧ IsSepClosed (ResidueField C) ∧
      ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
        (i : K →+* Ω) (η' : FractionRing C →+* Ω),
        η'.comp (dvrCompletionFractionMap D) = i.comp η ∧
        let q := Spec.map (CommRingCat.ofHom (algebraMap D C))
        let g := pullback.fst p f
        let ĝ := pullback.fst q g
        let γ := Spec.map (CommRingCat.ofHom η) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))
        let γ' := Spec.map (CommRingCat.ofHom (η'.comp (algebraMap C (FractionRing C))))
        let δ := Spec.map (CommRingCat.ofHom (o.comp (residue D)))
        let o' := o.comp (dvrCompletionResidueEquiv D).symm.toRingHom
        let δ' := Spec.map (CommRingCat.ofHom (o'.comp (residue C)))
        ∃ (qη : pullback γ' ĝ ⟶ pullback γ g)
          (qs : pullback δ' ĝ ⟶ pullback δ g),
          IsPullback qη (pullback.fst γ' ĝ) (pullback.fst γ g)
            (Spec.map (CommRingCat.ofHom i)) ∧
          qη ≫ pullback.snd γ g ≫ pullback.snd p f =
            pullback.snd γ' ĝ ≫ pullback.snd q g ≫ pullback.snd p f ∧
          IsPullback qs (pullback.fst δ' ĝ) (pullback.fst δ g)
            (Spec.map (CommRingCat.ofHom (RingHom.id k))) ∧
          qs ≫ pullback.snd δ g ≫ pullback.snd p f =
            pullback.snd δ' ĝ ≫ pullback.snd q g ≫ pullback.snd p f ∧
          (FiniteEtale.pullback qη).IsEquivalence ∧
          (FiniteEtale.pullback qs).IsEquivalence ∧
          (FiniteEtale.pullback (pullback.snd δ' ĝ)).IsEquivalence ∧
          (FiniteEtale.pullback (pullback.fst ĝ δ')).IsEquivalence := by
  obtain ⟨hC, hDVR, hH, hComplete, hSepC, Ω, hΩ, hΩclosed, i, η', hfield, hring⟩ :=
    exists_dvrCompletionFieldComparison D η
  refine ⟨hC, hDVR, hH, hComplete, hSepC, Ω, hΩ, hΩclosed, i, η', hfield, ?_⟩
  dsimp only
  let C := AdicCompletion (maximalIdeal D) D
  let c : D →+* C := algebraMap D C
  let β : C →+* Ω := η'.comp (algebraMap C (FractionRing C))
  let α : D →+* K := η.comp (algebraMap D (FractionRing D))
  let q := Spec.map (CommRingCat.ofHom c)
  let g := pullback.fst p f
  let ĝ := pullback.fst q g
  let γ := Spec.map (CommRingCat.ofHom η) ≫
    Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))
  let γ' := Spec.map (CommRingCat.ofHom β)
  let δ := Spec.map (CommRingCat.ofHom (o.comp (residue D)))
  let o' : ResidueField C →+* k := o.comp (dvrCompletionResidueEquiv D).symm.toRingHom
  let δ' := Spec.map (CommRingCat.ofHom (o'.comp (residue C)))
  have hp : ĝ ≫ q = pullback.snd q g ≫ g := pullback.condition
  have hcart : IsPullback (pullback.snd q g) ĝ g q :=
    (IsPullback.of_hasPullback q g).flip
  have hgeneric : γ' ≫ q = Spec.map (CommRingCat.ofHom i) ≫ γ := by
    have hcat : CommRingCat.ofHom c ≫ CommRingCat.ofHom β =
        CommRingCat.ofHom α ≫ CommRingCat.ofHom i :=
      congrArg CommRingCat.ofHom hring
    have hγ : γ = Spec.map (CommRingCat.ofHom α) :=
      (Spec.map_comp (CommRingCat.ofHom (algebraMap D (FractionRing D)))
        (CommRingCat.ofHom η)).symm
    change Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom c) = _
    rw [← Spec.map_comp, hcat, Spec.map_comp, hγ]
  have hclosedRing : (o'.comp (residue C)).comp c = o.comp (residue D) := by
    apply RingHom.ext
    intro d
    change o ((dvrCompletionResidueEquiv D).symm (residue C (c d))) = o (residue D d)
    rw [← dvrCompletionResidueEquiv_residue, RingEquiv.symm_apply_apply]
  have hclosed : δ' ≫ q = Spec.map (CommRingCat.ofHom (RingHom.id k)) ≫ δ := by
    have hcat : CommRingCat.ofHom c ≫ CommRingCat.ofHom (o'.comp (residue C)) =
        CommRingCat.ofHom (o.comp (residue D)) :=
      congrArg CommRingCat.ofHom hclosedRing
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 (Spec (.of k)) := by
      change Spec.map (𝟙 (CommRingCat.of k)) = _
      exact Spec.map_id _
    change Spec.map (CommRingCat.ofHom (o'.comp (residue C))) ≫
      Spec.map (CommRingCat.ofHom c) = _
    rw [← Spec.map_comp, hcat, hid, Category.id_comp]
  let qη := familyGeometricFiberMap g ĝ (pullback.snd q g) q hp γ' γ i hgeneric
  let qs := familyGeometricFiberMap g ĝ (pullback.snd q g) q hp δ' δ (RingHom.id k) hclosed
  have : IsProper g := inferInstance
  have : IsProper ĝ := inferInstance
  have hδ' : δ' = Spec.map (CommRingCat.ofHom o') ≫
      Spec.map (CommRingCat.ofHom (residue C)) := by
    change Spec.map (CommRingCat.ofHom (residue C) ≫ CommRingCat.ofHom o') = _
    exact Spec.map_comp _ _
  have hcompleteFiber : (FiniteEtale.pullback (pullback.fst ĝ δ')).IsEquivalence :=
    FiniteEtale.pullback_geometricClosedFiber_isEquivalence_of_isAdicComplete C ĝ δ' o' hδ'
  have hcompleteFiber' : (FiniteEtale.pullback (pullback.snd δ' ĝ)).IsEquivalence := by
    let e := pullbackSymmetry δ' ĝ
    let E : FiniteEtale (pullback ĝ δ') ≌ FiniteEtale (pullback δ' ĝ) :=
      MorphismProperty.Over.pullbackIso
        (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e.symm
    have hE : (FiniteEtale.pullback e.hom).IsEquivalence := E.isEquivalence_functor
    let comparison : FiniteEtale.pullback (pullback.snd δ' ĝ) ≅
        FiniteEtale.pullback (pullback.fst ĝ δ') ⋙ FiniteEtale.pullback e.hom :=
      MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
        e.hom (pullback.fst ĝ δ') (pullback.snd δ' ĝ)
        (pullbackSymmetry_hom_comp_fst δ' ĝ).symm
    exact Functor.isEquivalence_of_iso comparison.symm
  refine ⟨qη, qs, ?_, ?_, ?_, ?_, ?_, ?_, hcompleteFiber', hcompleteFiber⟩
  · exact familyGeometricFiberMap_isPullback g ĝ (pullback.snd q g) q hp
      γ' γ i hgeneric hcart
  · simpa only [Category.assoc] using
      congrArg (fun a => a ≫ pullback.snd p f)
        (familyGeometricFiberMap_snd g ĝ (pullback.snd q g) q hp γ' γ i hgeneric)
  · exact familyGeometricFiberMap_isPullback g ĝ (pullback.snd q g) q hp
      δ' δ (RingHom.id k) hclosed hcart
  · simpa only [Category.assoc] using
      congrArg (fun a => a ≫ pullback.snd p f)
        (familyGeometricFiberMap_snd g ĝ (pullback.snd q g) q hp
          δ' δ (RingHom.id k) hclosed)
  · exact pullback_familyGeometricFiberMap_isEquivalence g ĝ (pullback.snd q g) q hp
      γ' γ i hgeneric hcart
  · exact pullback_familyGeometricFiberMap_isEquivalence g ĝ (pullback.snd q g) q hp
      δ' δ (RingHom.id k) hclosed hcart

end EtaleFundamentalGroups.StrictHenselian
