/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionGeometricLift
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompletionColimitSpecialization
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition

/-!
# The original proper family and its completion-colimit comparison

For an arbitrary henselian local ring with separably closed residue field,
the constructed faithfully flat completion colimit supplies an actual
geometric generic lift. The native residue isomorphism supplies its closed
point. Both geometric-fiber comparisons are Cartesian and retain the
original total-space projections. The proved closed-fiber comparison over
the actual colimit supplies the two orientations of its restriction
equivalence. No Noetherian or valuation hypothesis is placed on the
original henselian ring.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AlgebraicGeometry.HenselianNoetherianImageStages

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- The actual completion-colimit construction compares both specified
geometric fibers of an arbitrary proper henselian family, preserving the
original total space and both orientations of the closed-fiber equivalence. -/
theorem exists_completionColimitFamilyComparison
    (R A : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (p : Spec (CommRingCat.of A) ⟶ S)
    {K k : Type u} [Field K] [IsSepClosed K] [Field k] [IsSepClosed k]
    (ψ : A →+* K) (o : ResidueField A →+* k) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L)
      (β : K →+* L) (α : completionColimit R A →+* L),
      α.comp (completionBaseMap R A).hom = β.comp ψ ∧
        let q := Spec.map (completionBaseMap R A)
        let g := pullback.fst p f
        let ĝ := pullback.fst q g
        let γ := Spec.map (CommRingCat.ofHom ψ)
        let γ' := Spec.map (CommRingCat.ofHom α)
        let δ := Spec.map (CommRingCat.ofHom (o.comp (residue A)))
        let o' := o.comp (completionResidueEquiv R A).toRingHom
        let δ' := Spec.map (CommRingCat.ofHom (o'.comp (residue (completionColimit R A))))
        ∃ (qη : pullback γ' ĝ ⟶ pullback γ g)
          (qs : pullback δ' ĝ ⟶ pullback δ g),
          IsPullback qη (pullback.fst γ' ĝ) (pullback.fst γ g)
            (Spec.map (CommRingCat.ofHom β)) ∧
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
  obtain ⟨L, hL, hLc, β, α, hring⟩ := exists_completionGeometricLift R A ψ
  refine ⟨L, hL, hLc, β, α, hring, ?_⟩
  dsimp only
  let q := Spec.map (completionBaseMap R A)
  let g := pullback.fst p f
  let ĝ := pullback.fst q g
  let γ := Spec.map (CommRingCat.ofHom ψ)
  let γ' := Spec.map (CommRingCat.ofHom α)
  let δ := Spec.map (CommRingCat.ofHom (o.comp (residue A)))
  let o' : ResidueField (completionColimit R A) →+* k :=
    o.comp (completionResidueEquiv R A).toRingHom
  let δ' := Spec.map (CommRingCat.ofHom (o'.comp (residue (completionColimit R A))))
  have hp : ĝ ≫ q = pullback.snd q g ≫ g := pullback.condition
  have hcart : IsPullback (pullback.snd q g) ĝ g q :=
    (IsPullback.of_hasPullback q g).flip
  have hgeneric : γ' ≫ q = Spec.map (CommRingCat.ofHom β) ≫ γ := by
    have hcat : completionBaseMap R A ≫ CommRingCat.ofHom α =
        CommRingCat.ofHom ψ ≫ CommRingCat.ofHom β :=
      CommRingCat.hom_ext hring
    change Spec.map (CommRingCat.ofHom α) ≫ Spec.map (completionBaseMap R A) = _
    exact (Spec.map_comp (completionBaseMap R A) (CommRingCat.ofHom α)).symm.trans
      ((congrArg Spec.map hcat).trans
        (Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)))
  have hclosedRing : (o'.comp (residue (completionColimit R A))).comp
      (completionBaseMap R A).hom = o.comp (residue A) := by
    apply RingHom.ext
    intro a
    exact congrArg o (completionResidueEquiv_base_residue R A a)
  have hclosed : δ' ≫ q = Spec.map (CommRingCat.ofHom (RingHom.id k)) ≫ δ := by
    have hcat : completionBaseMap R A ≫
        CommRingCat.ofHom (o'.comp (residue (completionColimit R A))) =
      CommRingCat.ofHom (o.comp (residue A)) := CommRingCat.hom_ext hclosedRing
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 (Spec (.of k)) := by
      change Spec.map (𝟙 (CommRingCat.of k)) = _
      exact Spec.map_id _
    change Spec.map (CommRingCat.ofHom (o'.comp (residue (completionColimit R A)))) ≫
      Spec.map (completionBaseMap R A) = _
    rw [hid, Category.id_comp]
    exact (Spec.map_comp (completionBaseMap R A)
      (CommRingCat.ofHom (o'.comp (residue (completionColimit R A))))).symm.trans
        (congrArg Spec.map hcat)
  let qη := familyGeometricFiberMap g ĝ (pullback.snd q g) q hp γ' γ β hgeneric
  let qs := familyGeometricFiberMap g ĝ (pullback.snd q g) q hp δ' δ (RingHom.id k) hclosed
  have : IsProper g := inferInstance
  have : IsProper ĝ := inferInstance
  have hδ' : δ' = Spec.map (CommRingCat.ofHom o') ≫
      Spec.map (CommRingCat.ofHom (residue (completionColimit R A))) := by
    change Spec.map (CommRingCat.ofHom (residue (completionColimit R A)) ≫
      CommRingCat.ofHom o') = _
    exact Spec.map_comp _ _
  have hclosedFiber : (FiniteEtale.pullback (pullback.fst ĝ δ')).IsEquivalence :=
    FiniteEtale.pullback_geometricClosedFiber_isEquivalence_completionColimit
      R A ĝ δ' o' hδ'
  have hclosedFiber' : (FiniteEtale.pullback (pullback.snd δ' ĝ)).IsEquivalence := by
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
  refine ⟨qη, qs, ?_, ?_, ?_, ?_, ?_, ?_, hclosedFiber', hclosedFiber⟩
  · exact familyGeometricFiberMap_isPullback g ĝ (pullback.snd q g) q hp
      γ' γ β hgeneric hcart
  · simpa only [Category.assoc] using
      congrArg (fun a => a ≫ pullback.snd p f)
        (familyGeometricFiberMap_snd g ĝ (pullback.snd q g) q hp γ' γ β hgeneric)
  · exact familyGeometricFiberMap_isPullback g ĝ (pullback.snd q g) q hp
      δ' δ (RingHom.id k) hclosed hcart
  · simpa only [Category.assoc] using
      congrArg (fun a => a ≫ pullback.snd p f)
        (familyGeometricFiberMap_snd g ĝ (pullback.snd q g) q hp
          δ' δ (RingHom.id k) hclosed)
  · exact pullback_familyGeometricFiberMap_isEquivalence g ĝ (pullback.snd q g) q hp
      γ' γ β hgeneric hcart
  · exact pullback_familyGeometricFiberMap_isEquivalence g ĝ (pullback.snd q g) q hp
      δ' δ (RingHom.id k) hclosed hcart

end EtaleFundamentalGroups.StrictHenselian
