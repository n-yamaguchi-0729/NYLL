/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilyGeometricFiberCartesian
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationNaturality
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationLiftValuation
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# The actual valuation family and its geometric fibers

The existing valuation factorization of a chosen strict-local lift supplies
the valuation ring. Base change of the original proper family then gives
its actual generic fiber, which is isomorphic to the original generic
fiber, and a common geometric closed fiber. The latter maps to both the
original special fiber and the valuation residue fiber by cartesian
field-extension squares. Both actual pullback functors are equivalences.

This supplies the family and field comparisons in Stacks 58.16.3
(https://stacks.math.columbia.edu/tag/0C0M). It does not assume or assert
the proper closed-fiber equivalence used to identify specialization maps.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- The specified lift produces an actual valuation family, its unchanged
generic fiber, and the two proper field-extension comparisons at the closed
fiber. All maps retain their projections to the original total space. -/
theorem exists_valuationFamily_of_specializationLift
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    {Ωs Ωt : Type u} [Field Ωs] [IsSepClosed Ωs]
    [Field Ωt] [IsAlgClosed Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom) :
    ∃ (V : ValuationSubring Ωt) (_ : HenselianLocalRing V),
      IsAlgClosed (ResidueField V) ∧
      ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
        (j : Ωs →+* k) (o : ResidueField V →+* k)
        (α : geometricStalk
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* V),
        IsLocalHom α ∧ (algebraMap V Ωt).comp α = ψ ∧
        (o.comp (residue V)).comp α = j.comp
          (geometricStalkEvaluation
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom ∧
        let p := Spec.map (CommRingCat.ofHom α) ≫ localGeometricStalkToScheme s
        let g := pullback.fst p f
        let γ := Spec.map (CommRingCat.ofHom (algebraMap V Ωt))
        let δ := Spec.map (CommRingCat.ofHom (o.comp (residue V)))
        let ρ := Spec.map (CommRingCat.ofHom (residue V))
        ∃ (qη : pullback γ g ⟶ pullback t f)
          (qs : pullback δ g ⟶ pullback s f)
          (qr : pullback δ g ⟶ pullback ρ g),
          IsPullback qη (pullback.fst γ g) (pullback.fst t f) (𝟙 _) ∧
          qη ≫ pullback.snd t f = pullback.snd γ g ≫ pullback.snd p f ∧
          IsIso qη ∧
          IsPullback qs (pullback.fst δ g) (pullback.fst s f)
            (Spec.map (CommRingCat.ofHom j)) ∧
          qs ≫ pullback.snd s f = pullback.snd δ g ≫ pullback.snd p f ∧
          IsPullback qr (pullback.fst δ g) (pullback.fst ρ g)
            (Spec.map (CommRingCat.ofHom o)) ∧
          qr ≫ pullback.snd ρ g = pullback.snd δ g ∧
          (FiniteEtale.pullback qs).IsEquivalence ∧
          (FiniteEtale.pullback qr).IsEquivalence := by
  obtain ⟨V, hV, hVr, k, hk, hkc, j, o, α, hα, hη, hρ, hg, hs⟩ :=
    exists_strictlyHenselianValuation_of_specializationLift s t h ψ hψ
  refine ⟨V, hV, hVr, k, hk, hkc, j, o, α, hα, hη, hρ, ?_⟩
  dsimp only
  let p := Spec.map (CommRingCat.ofHom α) ≫ localGeometricStalkToScheme s
  let g := pullback.fst p f
  let γ := Spec.map (CommRingCat.ofHom (algebraMap V Ωt))
  let δ := Spec.map (CommRingCat.ofHom (o.comp (residue V)))
  let ρ := Spec.map (CommRingCat.ofHom (residue V))
  have hp : g ≫ p = pullback.snd p f ≫ f := pullback.condition
  have hcart : IsPullback (pullback.snd p f) g f p :=
    (IsPullback.of_hasPullback p f).flip
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id Ωt)) =
      𝟙 (Spec (.of Ωt)) := by
    change Spec.map (𝟙 (CommRingCat.of Ωt)) = _
    exact Spec.map_id _
  have hgeneric : γ ≫ p = Spec.map (CommRingCat.ofHom (RingHom.id Ωt)) ≫ t := by
    rw [hid, Category.id_comp]
    exact hg
  let qη := familyGeometricFiberMap f g (pullback.snd p f) p hp γ t
    (RingHom.id Ωt) hgeneric
  let qs := familyGeometricFiberMap f g (pullback.snd p f) p hp δ s j hs
  have hidg : g ≫ 𝟙 _ = 𝟙 _ ≫ g := by
    rw [Category.comp_id, Category.id_comp]
  have hresidue : δ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom o) ≫ ρ := by
    rw [Category.comp_id]
    change Spec.map (CommRingCat.ofHom (residue V) ≫ CommRingCat.ofHom o) = _
    exact Spec.map_comp _ _
  let qr := familyGeometricFiberMap g g (𝟙 _) (𝟙 _) hidg δ ρ o hresidue
  have hηcart : IsPullback qη (pullback.fst γ g) (pullback.fst t f) (𝟙 _) := by
    simpa only [hid] using
      familyGeometricFiberMap_isPullback f g (pullback.snd p f) p hp γ t
        (RingHom.id Ωt) hgeneric hcart
  have hrcart : IsPullback (𝟙 _) g g (𝟙 _) := IsPullback.of_id_fst (f := g)
  have : IsProper g := inferInstance
  refine ⟨qη, qs, qr, hηcart, ?_, hηcart.isIso_fst_of_isIso, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact familyGeometricFiberMap_snd f g (pullback.snd p f) p hp γ t
      (RingHom.id Ωt) hgeneric
  · exact familyGeometricFiberMap_isPullback f g (pullback.snd p f) p hp δ s j hs hcart
  · exact familyGeometricFiberMap_snd f g (pullback.snd p f) p hp δ s j hs
  · exact familyGeometricFiberMap_isPullback g g (𝟙 _) (𝟙 _) hidg δ ρ o hresidue hrcart
  · exact (familyGeometricFiberMap_snd g g (𝟙 _) (𝟙 _) hidg δ ρ o hresidue).trans
      (Category.comp_id _)
  · exact pullback_familyGeometricFiberMap_isEquivalence f g (pullback.snd p f) p hp
      δ s j hs hcart
  · exact pullback_familyGeometricFiberMap_isEquivalence g g (𝟙 _) (𝟙 _) hidg
      δ ρ o hresidue hrcart

end EtaleFundamentalGroups.StrictHenselian
