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
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationLiftDVR
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The actual strict henselian DVR family and its geometric fibers

The existing chosen-lift factorization supplies the strict henselian DVR,
its actual fraction and residue fields, and the common algebraically closed
extensions. Base change of the original proper family gives cartesian maps
from the resulting geometric generic and closed fibers to the original
fibers. The common closed fiber also maps to the actual DVR residue fiber.
All three actual finite étale pullback functors are equivalences.

This supplies the family and field comparisons in Stacks 58.16.4
(https://stacks.math.columbia.edu/tag/0C0N). Identification of the
specialization homomorphisms still requires the proper closed-fiber
equivalence; no such equivalence is assumed here.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- The specified lift produces an actual strict henselian DVR family.
Its geometric generic fiber and a common geometric closed fiber compare
with the original fibers by actual cartesian field-extension maps. -/
theorem exists_dvrFamily_of_specializationLift
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f]
    {Ωs Ωt : Type u} [Field Ωs] [IsSepClosed Ωs]
    [Field Ωt] [IsSepClosed Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (i : Ωt →+* K) (j : Ωs →+* k)
      (D : CommRingCat.{u}) (_ : IsDomain D) (_ : HenselianLocalRing D),
      IsDiscreteValuationRing D ∧ IsSepClosed (ResidueField D) ∧
      ∃ (α : geometricStalk
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* D)
        (η : FractionRing D →+* K) (o : ResidueField D →+* k),
        IsLocalHom α ∧
        η.comp ((algebraMap D (FractionRing D)).comp α) = i.comp ψ ∧
        (o.comp (residue D)).comp α = j.comp
          (geometricStalkEvaluation
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom ∧
        let p := Spec.map (CommRingCat.ofHom α) ≫ localGeometricStalkToScheme s
        let g := pullback.fst p f
        let γ := Spec.map (CommRingCat.ofHom η) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))
        let δ := Spec.map (CommRingCat.ofHom (o.comp (residue D)))
        let ρ := Spec.map (CommRingCat.ofHom (residue D))
        ∃ (qη : pullback γ g ⟶ pullback t f)
          (qs : pullback δ g ⟶ pullback s f)
          (qr : pullback δ g ⟶ pullback ρ g),
          IsPullback qη (pullback.fst γ g) (pullback.fst t f)
            (Spec.map (CommRingCat.ofHom i)) ∧
          qη ≫ pullback.snd t f = pullback.snd γ g ≫ pullback.snd p f ∧
          IsPullback qs (pullback.fst δ g) (pullback.fst s f)
            (Spec.map (CommRingCat.ofHom j)) ∧
          qs ≫ pullback.snd s f = pullback.snd δ g ≫ pullback.snd p f ∧
          IsPullback qr (pullback.fst δ g) (pullback.fst ρ g)
            (Spec.map (CommRingCat.ofHom o)) ∧
          qr ≫ pullback.snd ρ g = pullback.snd δ g ∧
          (FiniteEtale.pullback qη).IsEquivalence ∧
          (FiniteEtale.pullback qs).IsEquivalence ∧
          (FiniteEtale.pullback qr).IsEquivalence := by
  obtain ⟨K, hK, hKc, k, hk, hkc, i, j, D, hD, hH, hDVR, hDr,
    α, η, o, hα, hη, hρ, hg, hs⟩ :=
      exists_strictlyHenselianDVR_of_specializationLift s t h ψ hψ
  refine ⟨K, hK, hKc, k, hk, hkc, i, j, D, hD, hH, hDVR, hDr,
    α, η, o, hα, hη, hρ, ?_⟩
  dsimp only
  let p := Spec.map (CommRingCat.ofHom α) ≫ localGeometricStalkToScheme s
  let g := pullback.fst p f
  let γ := Spec.map (CommRingCat.ofHom η) ≫
    Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))
  let δ := Spec.map (CommRingCat.ofHom (o.comp (residue D)))
  let ρ := Spec.map (CommRingCat.ofHom (residue D))
  have hp : g ≫ p = pullback.snd p f ≫ f := pullback.condition
  have hcart : IsPullback (pullback.snd p f) g f p :=
    (IsPullback.of_hasPullback p f).flip
  have hgeneric : γ ≫ p = Spec.map (CommRingCat.ofHom i) ≫ t := by
    exact (Category.assoc _ _ _).trans hg
  let qη := familyGeometricFiberMap f g (pullback.snd p f) p hp γ t i hgeneric
  let qs := familyGeometricFiberMap f g (pullback.snd p f) p hp δ s j hs
  have hidg : g ≫ 𝟙 _ = 𝟙 _ ≫ g := by
    rw [Category.comp_id, Category.id_comp]
  have hresidue : δ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom o) ≫ ρ := by
    rw [Category.comp_id]
    change Spec.map (CommRingCat.ofHom (residue D) ≫ CommRingCat.ofHom o) = _
    exact Spec.map_comp _ _
  let qr := familyGeometricFiberMap g g (𝟙 _) (𝟙 _) hidg δ ρ o hresidue
  have hrcart : IsPullback (𝟙 _) g g (𝟙 _) := IsPullback.of_id_fst (f := g)
  have : IsProper g := inferInstance
  refine ⟨qη, qs, qr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact familyGeometricFiberMap_isPullback f g (pullback.snd p f) p hp
      γ t i hgeneric hcart
  · exact familyGeometricFiberMap_snd f g (pullback.snd p f) p hp γ t i hgeneric
  · exact familyGeometricFiberMap_isPullback f g (pullback.snd p f) p hp δ s j hs hcart
  · exact familyGeometricFiberMap_snd f g (pullback.snd p f) p hp δ s j hs
  · exact familyGeometricFiberMap_isPullback g g (𝟙 _) (𝟙 _) hidg δ ρ o hresidue hrcart
  · exact (familyGeometricFiberMap_snd g g (𝟙 _) (𝟙 _) hidg δ ρ o hresidue).trans
      (Category.comp_id _)
  · exact pullback_familyGeometricFiberMap_isEquivalence f g (pullback.snd p f) p hp
      γ t i hgeneric hcart
  · exact pullback_familyGeometricFiberMap_isEquivalence f g (pullback.snd p f) p hp
      δ s j hs hcart
  · exact pullback_familyGeometricFiberMap_isEquivalence g g (𝟙 _) (𝟙 _) hidg
      δ ρ o hresidue hrcart

end EtaleFundamentalGroups.StrictHenselian
